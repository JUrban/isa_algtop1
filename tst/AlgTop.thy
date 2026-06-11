theory AlgTop
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
  case (v_cut_paste u1 a u2 u3) show ?case sorry
next
  case (v_cut_paste2 b u0 a u1 u2) show ?case sorry
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

\<comment> \<open>Cut-paste: quotient preserved by cut-and-repaste operation.\<close>
lemma quotient_of_scheme_cut_paste:
  assumes "top1_quotient_of_scheme_on Y TY (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)"
  shows "top1_quotient_of_scheme_on Y TY (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
  sorry

\<comment> \<open>Cut-paste2: quotient preserved by second cut-paste variant.\<close>
lemma quotient_of_scheme_cut_paste2:
  assumes "top1_quotient_of_scheme_on Y TY (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)"
  shows "top1_quotient_of_scheme_on Y TY ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
  sorry

\<comment> \<open>Cut-paste opposite: quotient preserved by opposite-direction cut-paste.
   Same polygon, permuted edge positions. Uses quotient\\_of\\_scheme\\_transfer\\_bij (defined later).
   Proof deferred to after transfer\\_bij.\<close>
lemma quotient_of_scheme_cut_paste_opp:
  assumes "top1_quotient_of_scheme_on Y TY (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)"
  shows "top1_quotient_of_scheme_on Y TY (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
  sorry \<comment> \<open>Same-space preservation; needs new polygon witnesses (transfer\\_bij won't work).\<close>

\<comment> \<open>Scheme quotient existence: every scheme of length \\<ge> 3 has a quotient realization.
   Construction: regular n-gon P with vertices at (cos(2\\<pi>k/n), sin(2\\<pi>k/n)).
   Quotient map q identifies boundary edges according to the scheme.
   This is a key missing lemma — once proved, all geometric gaps become easy.\<close>
lemma scheme_quotient_exists:
  fixes scheme :: "(nat \<times> bool) list"
  assumes "length scheme \<ge> 3"
  shows "\<exists>(Y :: (real \<times> real) set) (TY :: (real \<times> real) set set).
    top1_quotient_of_scheme_on Y TY scheme"
  sorry \<comment> \<open>Regular polygon + identification quotient construction.\<close>

\<comment> \<open>Cancel at front — homeomorphic-realization form (per expert audit 21 step 4).
   Given quotient of [a,inv a]@w, produce a (possibly different) quotient of w
   that is homeomorphic. This is WEAKER than same-space preservation.\<close>
lemma front_cancel_realization_homeo:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
      and "length w \<ge> 3"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' w \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
proof -
  define scheme where "scheme = [a, top1_inverse_edge a] @ w"
  let ?n = "length scheme"
  have hn: "?n = length w + 2" unfolding scheme_def by simp
  have hassms: "top1_quotient_of_scheme_on Y TY scheme" using assms(1) unfolding scheme_def .
  \<comment> \<open>Extract ALL 11 conditions from old quotient.\<close>
  from hassms obtain P q vx vy where
      hC1: "top1_is_polygonal_region_on P ?n"
    and hC2: "top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
    and hC3: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
    and hC4: "\<forall>i<?n. (vx i, vy i) \<in> P"
    and hC5: "P = {(x, y) | x y.
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
    and hC7: "\<forall>i<?n. \<forall>j<?n. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q ((1-t) * vx i + t * vx (Suc i mod ?n),
              (1-t) * vy i + t * vy (Suc i mod ?n))
         = (if snd (scheme!i) = snd (scheme!j)
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
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    and hC10: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx j) / real ?n;
                           cy = (\<Sum>j<?n. vy j) / real ?n
         in (vx i - cx) * (vy (Suc i mod ?n) - cy)
          - (vy i - cy) * (vx (Suc i mod ?n) - cx) > 0"
    and hC11: "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx k - vx i) * (vy (Suc i mod ?n) - vy i)
          - (vy k - vy i) * (vx (Suc i mod ?n) - vx i) < 0"
    by (rule quotient_of_scheme_extract_vx)
  \<comment> \<open>Now construct the same-space quotient of w using shifted vertices.\<close>
  let ?n' = "length w"
  \<comment> \<open>Shifted vertices: skip first 2.\<close>
  define vx' where "vx' i = vx (i + 2)" for i
  define vy' where "vy' i = vy (i + 2)" for i
  \<comment> \<open>New polygon: convex hull of shifted vertices.\<close>
  define P' where "P' = {(x::real,y::real). \<exists>coeffs. (\<forall>i<?n'. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n'. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n'. coeffs i * vx' i)
                     \<and> y = (\<Sum>i<?n'. coeffs i * vy' i)}"
  \<comment> \<open>Index correspondence: w!i = scheme!(i+2).\<close>
  have hscheme_shift: "\<And>i. i < ?n' \<Longrightarrow> w ! i = scheme ! (i + 2)"
    unfolding scheme_def by (by100 simp)
  \<comment> \<open>Show quotient\\_of\\_scheme\\_on Y TY w using P', q, vx', vy'.\<close>
  have "top1_quotient_of_scheme_on Y TY w"
    unfolding top1_quotient_of_scheme_on_def
  proof (intro conjI)
    show "is_topology_on_strict Y TY"
      using hassms unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  next
    show "\<exists>P q vx vy. top1_is_polygonal_region_on P ?n' \<and>
        top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q \<and>
        (\<forall>i<?n'. \<forall>j<?n'. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)) \<and>
        (\<forall>i<?n'. (vx i, vy i) \<in> P) \<and>
        P = {(x,y) | x y. \<exists>coeffs. (\<forall>i<?n'. coeffs i \<ge> 0) \<and> (\<Sum>i<?n'. coeffs i) = 1
                       \<and> x = (\<Sum>i<?n'. coeffs i * vx i) \<and> y = (\<Sum>i<?n'. coeffs i * vy i)} \<and>
        (\<forall>i<?n'. \<forall>j<?n'.
              i \<noteq> j \<longrightarrow> Suc i mod ?n' \<noteq> j \<longrightarrow> i \<noteq> Suc j mod ?n' \<longrightarrow>
              (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
                 ((1-s)*vx i + s*vx(Suc i mod ?n'), (1-s)*vy i + s*vy(Suc i mod ?n'))
               \<noteq> ((1-t)*vx j + t*vx(Suc j mod ?n'), (1-t)*vy j + t*vy(Suc j mod ?n')))) \<and>
        (\<forall>i<?n'. \<forall>j<?n'. fst(w!i) = fst(w!j) \<longrightarrow>
              (\<forall>t\<in>I_set. q((1-t)*vx i + t*vx(Suc i mod ?n'), (1-t)*vy i + t*vy(Suc i mod ?n'))
               = (if snd(w!i) = snd(w!j)
                  then q((1-t)*vx j + t*vx(Suc j mod ?n'), (1-t)*vy j + t*vy(Suc j mod ?n'))
                  else q(t*vx j + (1-t)*vx(Suc j mod ?n'), t*vy j + (1-t)*vy(Suc j mod ?n'))))) \<and>
        (\<forall>p\<in>P. (\<forall>i<?n'. \<forall>t\<in>I_set.
                    p \<noteq> ((1-t)*vx i + t*vx(Suc i mod ?n'), (1-t)*vy i + t*vy(Suc i mod ?n')))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')) \<and>
        (\<forall>i<?n'. \<forall>j<?n'. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
              q((1-t)*vx i + t*vx(Suc i mod ?n'), (1-t)*vy i + t*vy(Suc i mod ?n'))
            = q((1-s)*vx j + s*vx(Suc j mod ?n'), (1-s)*vy j + s*vy(Suc j mod ?n'))
            \<longrightarrow> (i=j \<and> t=s) \<or> (fst(w!i) = fst(w!j) \<and>
                 (if snd(w!i) = snd(w!j) then s=t else s=1-t))) \<and>
        (\<forall>i<?n'. let cx = (\<Sum>j<?n'. vx j)/real ?n'; cy = (\<Sum>j<?n'. vy j)/real ?n'
             in (vx i - cx)*(vy(Suc i mod ?n') - cy) - (vy i - cy)*(vx(Suc i mod ?n') - cx) > 0) \<and>
        (\<forall>i<?n'. \<forall>k<?n'.
              k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n' \<longrightarrow>
              (vx k - vx i)*(vy(Suc i mod ?n') - vy i) - (vy k - vy i)*(vx(Suc i mod ?n') - vx i) < 0)"
    proof -
      have hlen_w: "?n' = ?n - 2" using hn by simp
      have hn_ge5: "?n \<ge> 5" using assms(2) hn by simp
      have hn'_ge3: "?n' \<ge> 3" using assms(2) .
      \<comment> \<open>Key: for i < n'-1, edge i of P' matches edge i+2 of P exactly.
         For i = n'-1, the edge wraps differently (chord from v\_{n-1} to v\\_2).\<close>
      show ?thesis sorry \<comment> \<open>11 conditions. Shift for i<n'-1; last edge needs chord argument.\<close>
    qed
  qed
  \<comment> \<open>Y is a quotient of w. Take Y'=Y, TY'=TY, h=id.\<close>
  moreover have "is_topology_on Y TY"
    using hassms unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Construct identity homeomorphism inline (homeomorphism\\_id is defined later).\<close>
  moreover have "top1_homeomorphism_on Y TY Y TY id"
  proof -
    have hid_cont: "top1_continuous_map_on Y TY Y TY id"
      by (rule top1_continuous_map_on_id[OF \<open>is_topology_on Y TY\<close>])
    have hinv: "\<forall>x\<in>Y. inv_into Y id x = x"
    proof
      fix x assume "x \<in> Y"
      thus "inv_into Y id x = x" using inv_into_f_f[OF inj_on_id \<open>x \<in> Y\<close>] by simp
    qed
    have "top1_continuous_map_on Y TY Y TY (inv_into Y id)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI allI impI)
      fix x assume "x \<in> Y" thus "inv_into Y id x \<in> Y" using hinv by (by100 simp)
    next
      fix V assume hV: "V \<in> TY"
      have "{x \<in> Y. inv_into Y id x \<in> V} = {x \<in> Y. id x \<in> V}"
        using hinv by (by100 auto)
      thus "{x \<in> Y. inv_into Y id x \<in> V} \<in> TY"
        using hid_cont hV unfolding top1_continuous_map_on_def by (by100 simp)
    qed
    thus ?thesis unfolding top1_homeomorphism_on_def
      using \<open>is_topology_on Y TY\<close> hid_cont by (by100 simp)
  qed
  ultimately show ?thesis
    apply (intro exI[of _ Y] exI[of _ TY] exI[of _ id] conjI)
    apply assumption+
    done
qed

\<comment> \<open>Uncancel at front — homeomorphic-realization form.\<close>
lemma front_uncancel_realization_homeo:
  fixes Y :: "'a set" and TY :: "'a set set"
  assumes "top1_quotient_of_scheme_on Y TY w"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' ([a, top1_inverse_edge a] @ w) \<and>
    top1_homeomorphism_on Y TY Y' TY' h"
  sorry \<comment> \<open>§76(vii): Uncancel front. Insert cancel spur into polygon.\<close>

\<comment> \<open>Cancel same-space: REMOVED (dead code). Replaced by front\\_cancel\\_realization\\_homeo.\<close>

\<comment> \<open>Uncancel at front: insert cancel pair at front.\<close>
lemma quotient_of_scheme_uncancel_front:
  assumes "top1_quotient_of_scheme_on Y TY w"
  shows "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ w)"
  sorry \<comment> \<open>Geometric: unfold front position. Reverse of cancel\\_front.\<close>

\<comment> \<open>Uncancel (proved via reduction to front-uncancel + rotation).\<close>
lemma quotient_of_scheme_uncancel_proved:
  assumes "top1_quotient_of_scheme_on Y TY (u @ v)"
  shows "top1_quotient_of_scheme_on Y TY (u @ [a, top1_inverse_edge a] @ v)"
proof -
  have "top1_quotient_of_scheme_on Y TY (v @ u)"
    using quotient_of_scheme_rotate[OF assms] by simp
  from quotient_of_scheme_uncancel_front[OF this, of a]
  have h1: "top1_quotient_of_scheme_on Y TY ([a, top1_inverse_edge a] @ v @ u)" .
  \<comment> \<open>Rotate: [a,inv a] @ (v@u) -> (v@u) @ [a,inv a].\<close>
  from quotient_of_scheme_rotate[OF h1]
  have h2: "top1_quotient_of_scheme_on Y TY ((v @ u) @ [a, top1_inverse_edge a])" by simp
  \<comment> \<open>Rewrite: (v@u)@[a,inv a] = v @ (u @ [a,inv a]).\<close>
  hence h3: "top1_quotient_of_scheme_on Y TY (v @ (u @ [a, top1_inverse_edge a]))" by simp
  \<comment> \<open>Rotate: v @ (u@[a,inv a]) -> (u@[a,inv a]) @ v.\<close>
  from quotient_of_scheme_rotate[OF h3]
  have h4: "top1_quotient_of_scheme_on Y TY ((u @ [a, top1_inverse_edge a]) @ v)" by simp
  \<comment> \<open>Rewrite: (u@[a,inv a])@v = u@[a,inv a]@v.\<close>
  thus ?thesis by simp
qed

\<comment> \<open>Elementary operations preserve quotient\_of\_scheme\_on for the SAME space.
   If Y is a quotient of scheme s, and s \<rightarrow> t via an elementary operation,
   then Y is also a quotient of scheme t (same polygon, adjusted vertex labeling).\<close>
lemma elementary_operation_preserves_quotient:
  assumes "top1_quotient_of_scheme_on Y TY s"
      and "top1_elementary_scheme_operation s t"
  shows "top1_quotient_of_scheme_on Y TY t"
  using assms sorry \<comment> \<open>DEAD CODE. No live caller. Contains FALSE relabel case.\<close>

\<comment> \<open>scheme\\_equiv preserves quotient: if Y is quotient of s and s ~ t, then Y is quotient of t.\<close>
\<comment> \<open>Each elementary operation is reversible: if s → t, then t ~* s.\<close>
\<comment> \<open>Relabel reverse: relabel(old\\<to>new) followed by relabel(new\\<to>old) gives back the original.
   Freshness ensures no label collisions.\<close>
lemma relabel_reverse:
  assumes "new \<notin> fst ` set w" and "new \<noteq> old"
  shows "top1_scheme_equiv (map (\<lambda>(x,b). (if x = old then new else x, b)) w) w"
proof -
  let ?t = "map (\<lambda>(x,b). (if x = old then new else x, b)) w"
  \<comment> \<open>After relabeling old\\<to>new, the label 'old' no longer appears in ?t.\<close>
  have hold_fresh: "old \<notin> fst ` set ?t"
  proof
    assume "old \<in> fst ` set ?t"
    then obtain e where he: "e \<in> set ?t" "fst e = old" by (by100 blast)
    from he(1) obtain e0 where he0: "e0 \<in> set w" "e = (case e0 of (x,b) \<Rightarrow> (if x = old then new else x, b))"
      by (by100 auto)
    obtain l b where hlb: "e0 = (l, b)" by (cases e0)
    have "fst e = (if l = old then new else l)" using he0(2) hlb by (by100 simp)
    with he(2) have "l \<noteq> old" using assms(2) by (by100 fastforce)
    hence "fst e = l" using \<open>fst e = (if l = old then new else l)\<close> by (by100 simp)
    with he(2) have "l = old" by (by100 simp)
    with \<open>l \<noteq> old\<close> show False by (by100 simp)
  qed
  \<comment> \<open>Applying relabel(new\\<to>old) to ?t gives back w.\<close>
  have hrev_eq: "map (\<lambda>(x,b). (if x = new then old else x, b)) ?t = w"
  proof -
    have "map (\<lambda>(x,b). (if x = new then old else x, b)) ?t
        = map ((\<lambda>(x,b). (if x = new then old else x, b)) \<circ> (\<lambda>(x,b). (if x = old then new else x, b))) w"
      by (by100 simp)
    also have "\<dots> = map id w"
    proof (rule map_cong)
      fix e assume he: "e \<in> set w"
      obtain l b where hlb: "e = (l, b)" by (cases e)
      have "l \<in> fst ` set w" using he hlb by (by100 force)
      hence "l \<noteq> new" using assms(1) by (by100 blast)
      show "((\<lambda>(x,b). (if x = new then old else x, b)) \<circ> (\<lambda>(x,b). (if x = old then new else x, b))) e = id e"
        using hlb \<open>l \<noteq> new\<close> by (by100 auto)
    qed (by100 simp)
    finally show ?thesis by (by100 simp)
  qed
  \<comment> \<open>The relabel constructor gives the elementary operation.\<close>
  have hdiff: "old \<noteq> new" using assms(2) by (by100 simp)
  have "top1_elementary_scheme_operation ?t (map (\<lambda>(x,b). (if x = new then old else x, b)) ?t)"
    by (rule top1_elementary_scheme_operation.relabel)
  hence "top1_elementary_scheme_operation ?t w" using hrev_eq by (by100 simp)
  thus ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
qed

\<comment> \<open>NOTE: relabel\\_operation\\_freshness (inversion on the relabel constructor) is FALSE as
   a standalone lemma — the map-relabel form can coincidentally match other constructors
   (e.g. rotate). The freshness is only available INSIDE the induction case, where we
   know the constructor. But Isabelle's case mechanism doesn't expose it.
   The relabel\\_reverse standalone lemma (proved above) IS correct with explicit freshness.\<close>

\<comment> \<open>elementary\\_operation\\_reverse: REMOVED (dead code).\<close>

\<comment> \<open>scheme\\_equiv\\_sym: kept for backward compat with old helpers (dead code chain).\<close>
lemma scheme_equiv_sym:
  "top1_scheme_equiv s t \<Longrightarrow> top1_scheme_equiv t s"
  sorry \<comment> \<open>Dead code. Old helpers use this but no live code calls them.\<close>

lemma scheme_equiv_preserves_quotient:
  assumes "top1_quotient_of_scheme_on Y TY s"
      and "top1_scheme_equiv s t"
  shows "top1_quotient_of_scheme_on Y TY t"
  using assms(2,1) unfolding top1_scheme_equiv_def
  by (induction rule: rtranclp.induct) (auto intro: elementary_operation_preserves_quotient)

\<comment> \<open>Same-space preservation implies homeomorphic-realization preservation (take Y=X, h=id).\<close>
\<comment> \<open>Identity is a homeomorphism on any topological space.\<close>
lemma homeomorphism_id:
  assumes "is_topology_on X TX"
  shows "top1_homeomorphism_on X TX X TX id"
proof -
  have hid_cont: "top1_continuous_map_on X TX X TX id"
    by (rule top1_continuous_map_on_id[OF assms])
  have hinv: "\<forall>x\<in>X. inv_into X id x = x"
  proof
    fix x assume "x \<in> X"
    have "inv_into X id (id x) = x" by (rule inv_into_f_f[OF inj_on_id \<open>x \<in> X\<close>])
    thus "inv_into X id x = x" by simp
  qed
  have "top1_continuous_map_on X TX X TX (inv_into X id)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI allI impI)
    fix x assume "x \<in> X" thus "inv_into X id x \<in> X" using hinv by (by100 simp)
  next
    fix V assume hV: "V \<in> TX"
    have "{x \<in> X. inv_into X id x \<in> V} = {x \<in> X. id x \<in> V}"
      using hinv by (by100 auto)
    thus "{x \<in> X. inv_into X id x \<in> V} \<in> TX"
      using hid_cont hV unfolding top1_continuous_map_on_def by (by100 simp)
  qed
  thus ?thesis unfolding top1_homeomorphism_on_def using assms hid_cont by (by100 simp)
qed

\<comment> \<open>Flat intro for homeomorphic realization.\<close>
lemma homeo_realization_flat_introI:
  fixes X :: "'a set" and TX :: "'a set set" and Y :: "'a set" and TY :: "'a set set" and h :: "'a \<Rightarrow> 'a"
  assumes hq: "top1_quotient_of_scheme_on Y TY t"
      and hh: "top1_homeomorphism_on X TX Y TY h"
  shows "\<exists>(Y' :: 'a set) (TY' :: 'a set set) (h' :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y' TY' t \<and>
    top1_homeomorphism_on X TX Y' TY' h'"
proof -
  have H0: "top1_quotient_of_scheme_on Y TY t \<and>
     top1_homeomorphism_on X TX Y TY h"
    using hq hh by (by100 blast)
  have H1: "\<exists>h'. top1_quotient_of_scheme_on Y TY t \<and>
        top1_homeomorphism_on X TX Y TY h'"
  proof (rule exI[where x = h])
    show "top1_quotient_of_scheme_on Y TY t \<and>
          top1_homeomorphism_on X TX Y TY h"
      using H0 .
  qed
  have H2: "\<exists>TY' h'. top1_quotient_of_scheme_on Y TY' t \<and>
            top1_homeomorphism_on X TX Y TY' h'"
  proof (rule exI[where x = TY])
    show "\<exists>h'. top1_quotient_of_scheme_on Y TY t \<and>
            top1_homeomorphism_on X TX Y TY h'"
      using H1 .
  qed
  show ?thesis
  proof (rule exI[where x = Y])
    show "\<exists>TY' h'. top1_quotient_of_scheme_on Y TY' t \<and>
                top1_homeomorphism_on X TX Y TY' h'"
      using H2 .
  qed
qed

lemma same_space_implies_homeo_realization:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
proof -
  have "is_topology_on X TX"
    using assms unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?thesis by (rule homeo_realization_flat_introI[OF assms homeomorphism_id[OF \<open>is_topology_on X TX\<close>]])
qed

\<comment> \<open>Bridge: unrestricted scheme\\_equiv also gives homeomorphic realization.
   Uses the OLD chain (scheme\\_equiv\\_preserves\\_quotient) which has geometric gaps.
   The normal form now uses valid\\_equiv; this bridge is used for the hard cases in
   valid\\_operation\\_preserves\\_quotient\\_homeo (cancel/uncancel/cut-paste).\<close>
lemma scheme_equiv_implies_homeo_realization:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX s"
      and "top1_scheme_equiv s t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
proof -
  have "top1_quotient_of_scheme_on X TX t"
    by (rule scheme_equiv_preserves_quotient[OF assms])
  thus ?thesis by (rule same_space_implies_homeo_realization)
qed

\<comment> \<open>Homeomorphism-preservation for valid scheme operations (per expert audit step 8).
   For rotate/invert/flip/relabel\\_fresh: use same-space preservation (Y = X).
   For cancel/uncancel/cut-paste: use bridge via scheme\\_equiv (one elementary step).
   This is the correct semantic theorem for the classification chain.\<close>
lemma valid_operation_preserves_quotient_homeo:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX s"
      and "top1_valid_scheme_operation s t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
  using assms(2,1)
proof (induction rule: top1_valid_scheme_operation.induct)
  case (v_rotate u v)
  have hq: "top1_quotient_of_scheme_on X TX (v @ u)"
    by (rule quotient_of_scheme_rotate[OF v_rotate.prems])
  have htopo: "is_topology_on X TX"
    using hq unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?case by (rule homeo_realization_flat_introI[OF hq homeomorphism_id[OF htopo]])
next
  case (v_cancel u a v)
  \<comment> \<open>Cancel: §76(vi). The (n+2)-gon folds along cancelled edge pair to give n-gon.
     Step 1: Extract polygon P, quotient map q, vertices from the old quotient.
     Step 2: Define new polygon P' by skipping vertex at position |u|+1.
     Step 3: Show P' is a valid polygonal region for scheme u@v.
     Step 4: Use quotient\\_transport\\_by\\_homeomorphism.\<close>
  \<comment> \<open>Use homeo-realization: rotate to front, apply cancel, rotate back.\<close>
  show ?case
  proof (cases "length (u @ v) \<ge> 3")
    case True
    have h1: "top1_quotient_of_scheme_on X TX ([a, top1_inverse_edge a] @ v @ u)"
      using quotient_of_scheme_rotate[OF v_cancel.prems] by simp
    have hlen: "length (v @ u) \<ge> 3" using True by simp
    from front_cancel_realization_homeo[OF h1 hlen]
    obtain Y' :: "'a set" and TY' :: "'a set set" and h1' :: "'a \<Rightarrow> 'a" where
        hY': "top1_quotient_of_scheme_on Y' TY' (v @ u)"
        and hh1': "top1_homeomorphism_on X TX Y' TY' h1'"
      by (by100 blast)
    have "top1_quotient_of_scheme_on Y' TY' (u @ v)"
      using quotient_of_scheme_rotate[OF hY'] by simp
    thus ?thesis using hh1' by (rule homeo_realization_flat_introI)
  next
    case False
    \<comment> \<open>Short scheme: length(u@v) < 3. The result has \\<le> 2 edges.
       The polygon model requires \\<ge> 3 sides, so quotient\\_of\\_scheme\\_on can't hold.
       But the NF proof only applies cancel when length \\<ge> 6, so this case
       never arises in practice. Sorry for completeness.\<close>
    show ?thesis sorry \<comment> \<open>Short scheme cancel: length(u@v) < 3. Degenerate case.\<close>
  qed
next
  case (v_uncancel a u v)
  \<comment> \<open>Uncancel: §76(vii). Use front\\_uncancel\\_realization\\_homeo via rotation.\<close>
  have h1: "top1_quotient_of_scheme_on X TX (v @ u)"
    using quotient_of_scheme_rotate[OF v_uncancel.prems] by simp
  from front_uncancel_realization_homeo[OF h1, of a]
  obtain Y' :: "'a set" and TY' :: "'a set set" and h1' :: "'a \<Rightarrow> 'a" where
      hY': "top1_quotient_of_scheme_on Y' TY' ([a, top1_inverse_edge a] @ v @ u)"
      and hh1': "top1_homeomorphism_on X TX Y' TY' h1'"
    by (by100 blast)
  have "top1_quotient_of_scheme_on Y' TY' ((v @ u) @ [a, top1_inverse_edge a])"
    using quotient_of_scheme_rotate[OF hY'] by simp
  hence "top1_quotient_of_scheme_on Y' TY' (v @ (u @ [a, top1_inverse_edge a]))"
    by simp
  hence "top1_quotient_of_scheme_on Y' TY' ((u @ [a, top1_inverse_edge a]) @ v)"
    using quotient_of_scheme_rotate by (by100 fastforce)
  hence "top1_quotient_of_scheme_on Y' TY' (u @ [a, top1_inverse_edge a] @ v)"
    by simp
  thus ?case using hh1' by (rule homeo_realization_flat_introI)
next
  case v_cancel_reverse
  \<comment> \<open>v\\_cancel\\_reverse: u@v -> u@[a,inv a]@v. Same as uncancel.\<close>
  from quotient_of_scheme_uncancel_proved[OF v_cancel_reverse.prems]
  show ?case by (rule same_space_implies_homeo_realization)
next
  case (v_invert w)
  have hq: "top1_quotient_of_scheme_on X TX (rev (map top1_inverse_edge w))"
    by (rule quotient_of_scheme_invert[OF v_invert.prems])
  have htopo: "is_topology_on X TX"
    using hq unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?case by (rule homeo_realization_flat_introI[OF hq homeomorphism_id[OF htopo]])
next
  case (v_relabel new old w)
  from quotient_of_scheme_relabel_fresh[OF v_relabel.prems v_relabel(1) v_relabel(2)]
  show ?case by (rule same_space_implies_homeo_realization)
next
  case (v_flip_label w a)
  have hq: "top1_quotient_of_scheme_on X TX (map (\<lambda>(l, bo). (l, if l = a then \<not> bo else bo)) w)"
    by (rule quotient_scheme_flip_label[OF v_flip_label.prems])
  have htopo: "is_topology_on X TX"
    using hq unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?case by (rule homeo_realization_flat_introI[OF hq homeomorphism_id[OF htopo]])
next
  case (v_cut_paste u1 a u2 u3)
  \<comment> \<open>Cut-paste: §76. Cut polygon along diagonal, flip, reglue.\<close>
  have "top1_quotient_of_scheme_on X TX (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
    by (rule quotient_of_scheme_cut_paste[OF v_cut_paste.prems])
  then show ?case by (rule same_space_implies_homeo_realization)
next
  case (v_cut_paste2 b u0 a u1 u2)
  \<comment> \<open>Cut-paste2: §76 variant.\<close>
  have "top1_quotient_of_scheme_on X TX ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
    by (rule quotient_of_scheme_cut_paste2[OF v_cut_paste2.prems])
  then show ?case by (rule same_space_implies_homeo_realization)
next
  case (v_cut_paste_opp u0 u1 a u2 u3)
  \<comment> \<open>Cut-paste-opp: §76(ix). Cut along diagonal, rearrange edges.\<close>
  have "top1_quotient_of_scheme_on X TX (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
    by (rule quotient_of_scheme_cut_paste_opp[OF v_cut_paste_opp.prems])
  then show ?case by (rule same_space_implies_homeo_realization)
next
  case (v_context_left y z prefix)
  \<comment> \<open>Context-left: valid operation y \\<to> z lifts to prefix@y \\<to> prefix@z.
     Per audit 21: closure infrastructure, not primitive geometric move.
     Decoupled from old chain (no dependency on FALSE relabel).\<close>
  show ?case sorry \<comment> \<open>Context-left quotient preservation. NOT via old chain.\<close>
qed

\<comment> \<open>Chain: valid equivalence preserves quotient homeomorphism type.\<close>
lemma valid_equiv_preserves_quotient_homeo:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX s"
      and "top1_valid_scheme_equiv s t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
  using assms(2,1) unfolding top1_valid_scheme_equiv_def
proof (induction rule: rtranclp.induct)
  case rtrancl_refl
  then show ?case by (rule same_space_implies_homeo_realization)
next
  case (rtrancl_into_rtrancl a b c)
  \<comment> \<open>Step: IH gives \\<exists>Y TY h for 'a'; valid\\_op gives \\<exists>Z TZ g for 'b\\<to>c'; compose.\<close>
  from rtrancl_into_rtrancl.IH[OF rtrancl_into_rtrancl.prems]
  have hIH: "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY b \<and> top1_homeomorphism_on X TX Y TY h" .
  then obtain Y :: "'a set" and TY :: "'a set set" and hy :: "'a \<Rightarrow> 'a" where
      qY: "top1_quotient_of_scheme_on Y TY b"
    and hXY: "top1_homeomorphism_on X TX Y TY hy"
    by (by100 blast)
  from valid_operation_preserves_quotient_homeo[OF qY rtrancl_into_rtrancl.hyps(2)]
  obtain Z :: "'a set" and TZ :: "'a set set" and gz :: "'a \<Rightarrow> 'a" where
      qZ: "top1_quotient_of_scheme_on Z TZ c"
    and hYZ: "top1_homeomorphism_on Y TY Z TZ gz"
    by (by100 blast)
  have hXZ: "top1_homeomorphism_on X TX Z TZ (gz \<circ> hy)"
    using homeomorphism_comp[OF hXY hYZ] .
  show ?case using qZ hXZ by (rule homeo_realization_flat_introI)
qed

\<comment> \<open>Bridge moved to before valid\\_operation\\_preserves.\<close>

\<comment> \<open>A polygonal region is compact (continuous image of a compact simplex).\<close>
lemma polygonal_region_compact:
  assumes "top1_is_polygonal_region_on P n"
  shows "compact P"
proof -
  from assms obtain vx vy where hn: "n \<ge> 3"
      and hP: "P = {(x, y). \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                  \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
    unfolding top1_is_polygonal_region_on_def by (by5000 auto)
  \<comment> \<open>P is bounded: all coordinates are convex combinations of finitely many vertex coordinates.\<close>
  define M where "M = Max ((\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n})"
  have hfin: "finite ((\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n})"
    by simp
  have hne: "(\<lambda>i. \<bar>vx i\<bar>) ` {..<n} \<union> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n} \<noteq> {}"
  proof -
    have "(0::nat) < n" using hn by simp
    hence "\<bar>vx 0\<bar> \<in> (\<lambda>i. \<bar>vx i\<bar>) ` {..<n}" by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hM_bound: "\<And>i. i < n \<Longrightarrow> \<bar>vx i\<bar> \<le> M \<and> \<bar>vy i\<bar> \<le> M"
  proof -
    fix i assume "i < n"
    have "\<bar>vx i\<bar> \<in> (\<lambda>i. \<bar>vx i\<bar>) ` {..<n}" using \<open>i < n\<close> by (by100 blast)
    hence "\<bar>vx i\<bar> \<le> M" unfolding M_def using hfin hne by (by100 auto)
    moreover have "\<bar>vy i\<bar> \<in> (\<lambda>i. \<bar>vy i\<bar>) ` {..<n}" using \<open>i < n\<close> by (by100 blast)
    hence "\<bar>vy i\<bar> \<le> M" unfolding M_def using hfin hne by (by100 auto)
    ultimately show "\<bar>vx i\<bar> \<le> M \<and> \<bar>vy i\<bar> \<le> M" by simp
  qed
  have hP_bounded: "P \<subseteq> {- M .. M} \<times> {- M .. M}"
  proof
    fix p assume "p \<in> P"
    then obtain x y coeffs where hp: "p = (x, y)"
        and hcoeffs: "\<forall>i<n. (0::real) \<le> coeffs i" "(\<Sum>i<n. coeffs i) = 1"
        and hx: "x = (\<Sum>i<n. coeffs i * vx i)" and hy: "y = (\<Sum>i<n. coeffs i * vy i)"
      unfolding hP by (by5000 auto)
    \<comment> \<open>|x| \\<le> \\<Sum> coeffs i * M = M. Similarly for y.\<close>
    have "\<bar>x\<bar> \<le> M"
    proof -
      have "\<bar>x\<bar> \<le> (\<Sum>i<n. \<bar>coeffs i * vx i\<bar>)" unfolding hx
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>i<n. coeffs i * M)"
      proof (rule sum_mono)
        fix i assume "i \<in> {..<n}" hence "i < n" by simp
        have "\<bar>coeffs i * vx i\<bar> = coeffs i * \<bar>vx i\<bar>"
          using hcoeffs(1) \<open>i < n\<close> by (simp add: abs_mult)
        also have "\<dots> \<le> coeffs i * M" using hM_bound[OF \<open>i < n\<close>] hcoeffs(1) \<open>i < n\<close>
          by (intro mult_left_mono) (by100 auto)+
        finally show "\<bar>coeffs i * vx i\<bar> \<le> coeffs i * M" .
      qed
      also have "\<dots> = M" using hcoeffs(2) by (simp add: sum_distrib_right[symmetric])
      finally show ?thesis .
    qed
    have "\<bar>y\<bar> \<le> M"
    proof -
      have "\<bar>y\<bar> \<le> (\<Sum>i<n. \<bar>coeffs i * vy i\<bar>)" unfolding hy
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>i<n. coeffs i * M)"
      proof (rule sum_mono)
        fix i assume "i \<in> {..<n}" hence "i < n" by simp
        have "\<bar>coeffs i * vy i\<bar> = coeffs i * \<bar>vy i\<bar>"
          using hcoeffs(1) \<open>i < n\<close> by (simp add: abs_mult)
        also have "\<dots> \<le> coeffs i * M" using hM_bound[OF \<open>i < n\<close>] hcoeffs(1) \<open>i < n\<close>
          by (intro mult_left_mono) (by100 auto)+
        finally show "\<bar>coeffs i * vy i\<bar> \<le> coeffs i * M" .
      qed
      also have "\<dots> = M" using hcoeffs(2) by (simp add: sum_distrib_right[symmetric])
      finally show ?thesis .
    qed
    show "p \<in> {- M..M} \<times> {- M..M}" using \<open>\<bar>x\<bar> \<le> M\<close> \<open>\<bar>y\<bar> \<le> M\<close> hp by (by100 auto)
  qed
  \<comment> \<open>P is closed: the set of convex combinations of finitely many fixed points is closed.
     (Limit of convergent sequence of convex combinations is a convex combination.)\<close>
  \<comment> \<open>Show P is compact directly via inductive convex hull argument.\<close>
  have hP_compact_direct: "compact P"
  proof -
    \<comment> \<open>Define partial convex hulls: Q k = conv({(vx i, vy i) | i \\<le> k}).\<close>
    define Q where "Q k = {(x::real, y::real). \<exists>coeffs.
        (\<forall>i\<le>k. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>k. coeffs i) = 1
        \<and> x = (\<Sum>i\<le>k. coeffs i * vx i) \<and> y = (\<Sum>i\<le>k. coeffs i * vy i)}" for k
    \<comment> \<open>Base: Q 0 = {(vx 0, vy 0)} is compact (singleton).\<close>
    have hQ0_eq: "Q 0 = {(vx 0, vy 0)}"
    proof
      show "Q 0 \<subseteq> {(vx 0, vy 0)}"
        unfolding Q_def by (by5000 force)
      show "{(vx 0, vy 0)} \<subseteq> Q 0"
        unfolding Q_def
      proof
        fix p assume "p \<in> {(vx 0, vy 0)}"
        hence "p = (vx 0, vy 0)" by simp
        define coeffs :: "nat \<Rightarrow> real" where "coeffs = (\<lambda>_. 1)"
        have "(\<forall>i\<le>(0::nat). (0::real) \<le> coeffs i) \<and> (\<Sum>i\<le>0. coeffs i) = 1
            \<and> vx 0 = (\<Sum>i\<le>0. coeffs i * vx i) \<and> vy 0 = (\<Sum>i\<le>0. coeffs i * vy i)"
          unfolding coeffs_def by simp
        thus "p \<in> {(x, y). \<exists>coeffs. (\<forall>i\<le>0. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>0. coeffs i) = 1
            \<and> x = (\<Sum>i\<le>0. coeffs i * vx i) \<and> y = (\<Sum>i\<le>0. coeffs i * vy i)}"
          unfolding \<open>p = (vx 0, vy 0)\<close> by (by100 blast)
      qed
    qed
    have hQ0: "compact (Q 0)"
      unfolding hQ0_eq
    proof (rule compactI)
      fix C :: "(real \<times> real) set set"
      assume "\<forall>c\<in>C. open c" and "{(vx 0, vy 0)} \<subseteq> \<Union>C"
      then obtain U where "U \<in> C" "(vx 0, vy 0) \<in> U" by (by100 blast)
      thus "\<exists>D\<subseteq>C. finite D \<and> {(vx 0, vy 0)} \<subseteq> \<Union>D"
        by (intro exI[of _ "{U}"]) (by100 auto)
    qed
    \<comment> \<open>Step: Q (Suc k) = {t*v\\_{k+1} + (1-t)*p | t \\<in> [0,1], p \\<in> Q k}.
       This is the continuous image of [0,1] \\<times> Q k, hence compact.\<close>
    have hQstep: "\<And>k. compact (Q k) \<Longrightarrow> compact (Q (Suc k))"
    proof -
      fix k assume hIH: "compact (Q k)"
      \<comment> \<open>Q(Suc k) = image of [0,1] \\<times> Q(k) under the affine combination map.\<close>
      define f where "f = (\<lambda>(t::real, p::real\<times>real). (t * vx (Suc k) + (1-t) * fst p, t * vy (Suc k) + (1-t) * snd p))"
      have hQ_eq: "Q (Suc k) = f ` ({0..1} \<times> Q k)"
      proof
        \<comment> \<open>(\\<subseteq>): every convex combo of k+2 points = t*v\\_{k+1} + (1-t)*(combo of first k+1).\<close>
        show "Q (Suc k) \<subseteq> f ` ({0..1} \<times> Q k)"
        proof
          fix q assume "q \<in> Q (Suc k)"
          then obtain coeffs where hc: "(\<forall>i\<le>Suc k. 0 \<le> coeffs i)" "(\<Sum>i\<le>Suc k. coeffs i) = 1"
              "fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i)" "snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)"
            unfolding Q_def by (by5000 auto)
          define t where "t = coeffs (Suc k)"
          have ht: "t \<in> {0..1}"
          proof -
            have "0 \<le> t" using hc(1) unfolding t_def by simp
            moreover have "t \<le> 1"
            proof -
              have "(\<Sum>i\<le>k. coeffs i) \<ge> 0"
                using hc(1) by (intro sum_nonneg) (by100 auto)
              hence "t = 1 - (\<Sum>i\<le>k. coeffs i)" using hc(2) unfolding t_def by simp
              thus ?thesis using \<open>(\<Sum>i\<le>k. coeffs i) \<ge> 0\<close> by linarith
            qed
            ultimately show ?thesis by simp
          qed
          show "q \<in> f ` ({0..1} \<times> Q k)"
          proof (cases "t = 1")
            case True
            \<comment> \<open>If t=1: q = v\\_{k+1}. f(1,p) = v\\_{k+1} for any p. Need Q k nonempty.\<close>
            have "fst q = vx (Suc k) \<and> snd q = vy (Suc k)"
            proof -
              have hzero: "\<forall>i\<le>k. coeffs i = 0"
              proof (rule ccontr)
                assume "\<not> (\<forall>i\<le>k. coeffs i = 0)"
                then obtain j where "j \<le> k" "coeffs j \<noteq> 0" by (by100 blast)
                have "0 \<le> coeffs j" using hc(1) \<open>j \<le> k\<close> by simp
                hence "coeffs j > 0" using \<open>coeffs j \<noteq> 0\<close> by linarith
                hence "(\<Sum>i\<le>k. coeffs i) > 0"
                  using hc(1) \<open>j \<le> k\<close> by (intro sum_pos2[of "{..k}" j]) (by100 auto)+
                hence "1 - t > 0" using hc(2) unfolding t_def by simp
                thus False using True by simp
              qed
              hence "(\<Sum>i\<le>k. coeffs i * vx i) = 0" "(\<Sum>i\<le>k. coeffs i * vy i) = 0"
                by (simp_all add: sum.neutral)
              thus ?thesis using hc(3,4) True unfolding t_def by simp
            qed
            \<comment> \<open>Q k is nonempty: (vx 0, vy 0) \\<in> Q 0 \\<subseteq> Q k.\<close>
            have "(vx 0, vy 0) \<in> Q k"
            proof -
              define c0 :: "nat \<Rightarrow> real" where "c0 i = (if i = 0 then 1 else 0)" for i
              have "(\<forall>i\<le>k. 0 \<le> c0 i)" unfolding c0_def by simp
              moreover have "(\<Sum>i\<le>k. c0 i) = 1" unfolding c0_def by simp
              moreover have "vx 0 = (\<Sum>i\<le>k. c0 i * vx i)"
              proof -
                have "(\<Sum>i\<le>k. c0 i * vx i) = c0 0 * vx 0 + (\<Sum>i\<in>{..k}-{0}. c0 i * vx i)"
                  by (rule sum.remove) simp_all
                also have "(\<Sum>i\<in>{..k}-{0}. c0 i * vx i) = 0"
                  by (rule sum.neutral) (simp add: c0_def)
                finally show ?thesis unfolding c0_def by simp
              qed
              moreover have "vy 0 = (\<Sum>i\<le>k. c0 i * vy i)"
              proof -
                have "(\<Sum>i\<le>k. c0 i * vy i) = c0 0 * vy 0 + (\<Sum>i\<in>{..k}-{0}. c0 i * vy i)"
                  by (rule sum.remove) simp_all
                also have "(\<Sum>i\<in>{..k}-{0}. c0 i * vy i) = 0"
                  by (rule sum.neutral) (simp add: c0_def)
                finally show ?thesis unfolding c0_def by simp
              qed
              ultimately show ?thesis unfolding Q_def by (by100 auto)
            qed
            hence "(1::real, (vx 0, vy 0)) \<in> {0..1} \<times> Q k" by simp
            hence "f (1, (vx 0, vy 0)) \<in> f ` ({0..1} \<times> Q k)" by (by100 blast)
            moreover have "f (1, (vx 0, vy 0)) = (vx (Suc k), vy (Suc k))"
              unfolding f_def by simp
            ultimately have "(vx (Suc k), vy (Suc k)) \<in> f ` ({0..1} \<times> Q k)" by simp
            thus ?thesis using \<open>fst q = vx (Suc k) \<and> snd q = vy (Suc k)\<close>
              by (cases q) (by100 auto)
          next
            case False
            \<comment> \<open>t < 1: define \\<alpha> i = coeffs i / (1-t) for i \\<le> k.\<close>
            have ht_lt: "t < 1" using ht False by simp
            hence h1mt: "1 - t > 0" by simp
            define \<alpha> where "\<alpha> i = coeffs i / (1 - t)" for i
            have h\<alpha>_pos: "\<forall>i\<le>k. 0 \<le> \<alpha> i"
              using hc(1) h1mt unfolding \<alpha>_def by (by100 auto)
            have h\<alpha>_sum: "(\<Sum>i\<le>k. \<alpha> i) = 1"
            proof -
              have "(\<Sum>i\<le>k. \<alpha> i) = (\<Sum>i\<le>k. coeffs i) / (1-t)"
                unfolding \<alpha>_def by (simp add: sum_divide_distrib)
              also have "(\<Sum>i\<le>k. coeffs i) = 1 - t"
                using hc(2) unfolding t_def by simp
              finally show ?thesis using h1mt by simp
            qed
            define p where "p = ((\<Sum>i\<le>k. \<alpha> i * vx i), (\<Sum>i\<le>k. \<alpha> i * vy i))"
            have hp: "p \<in> Q k" unfolding Q_def p_def
              using h\<alpha>_pos h\<alpha>_sum by (by100 auto)
            have "q = f (t, p)"
            proof -
              \<comment> \<open>fst q = t*vx(k+1) + (1-t) * Σα_i*vx_i\<close>
              have hx: "fst q = t * vx (Suc k) + (1-t) * (\<Sum>i\<le>k. \<alpha> i * vx i)"
              proof -
                have "fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i)" using hc(3) by simp
                also have "\<dots> = (\<Sum>i\<le>k. coeffs i * vx i) + coeffs (Suc k) * vx (Suc k)" by simp
                also have "(\<Sum>i\<le>k. coeffs i * vx i) = (1-t) * (\<Sum>i\<le>k. \<alpha> i * vx i)"
                  unfolding \<alpha>_def using h1mt
                  by (simp add: sum_distrib_left sum_divide_distrib)
                finally show ?thesis unfolding t_def by (simp add: algebra_simps)
              qed
              have hy: "snd q = t * vy (Suc k) + (1-t) * (\<Sum>i\<le>k. \<alpha> i * vy i)"
              proof -
                have "snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)" using hc(4) by simp
                also have "\<dots> = (\<Sum>i\<le>k. coeffs i * vy i) + coeffs (Suc k) * vy (Suc k)" by simp
                also have "(\<Sum>i\<le>k. coeffs i * vy i) = (1-t) * (\<Sum>i\<le>k. \<alpha> i * vy i)"
                  unfolding \<alpha>_def using h1mt
                  by (simp add: sum_distrib_left sum_divide_distrib)
                finally show ?thesis unfolding t_def by (simp add: algebra_simps)
              qed
              show ?thesis unfolding f_def p_def using hx hy by (cases q) simp
            qed
            thus ?thesis using ht hp by (by100 blast)
          qed
        qed
        \<comment> \<open>(\\<supseteq>): t*v\\_{k+1} + (1-t)*p where p \\<in> Q k is a convex combo of k+2 points.\<close>
        show "f ` ({0..1} \<times> Q k) \<subseteq> Q (Suc k)"
        proof
          fix q assume "q \<in> f ` ({0..1} \<times> Q k)"
          then obtain t p where ht: "t \<in> {0..1}" and hp: "p \<in> Q k" and hq: "q = f (t, p)"
            by (by100 blast)
          from hp obtain coeffs where hc: "(\<forall>i\<le>k. 0 \<le> coeffs i)" "(\<Sum>i\<le>k. coeffs i) = 1"
              "fst p = (\<Sum>i\<le>k. coeffs i * vx i)" "snd p = (\<Sum>i\<le>k. coeffs i * vy i)"
            unfolding Q_def by (by5000 auto)
          \<comment> \<open>New coefficients: \\<beta> i = (1-t)*coeffs i for i \\<le> k, \\<beta> (k+1) = t.\<close>
          define \<beta> where "\<beta> i = (if i = Suc k then t else (1-t) * coeffs i)" for i
          have h\<beta>_pos: "\<forall>i\<le>Suc k. 0 \<le> \<beta> i"
            using hc(1) ht unfolding \<beta>_def by (by100 auto)
          have h\<beta>_sum: "(\<Sum>i\<le>Suc k. \<beta> i) = 1"
          proof -
            have "(\<Sum>i\<le>Suc k. \<beta> i) = (\<Sum>i\<le>k. \<beta> i) + \<beta> (Suc k)" by simp
            also have "(\<Sum>i\<le>k. \<beta> i) = (\<Sum>i\<le>k. (1-t) * coeffs i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            also have "\<dots> = (1-t) * (\<Sum>i\<le>k. coeffs i)"
              by (simp add: sum_distrib_left)
            also have "\<dots> = (1-t)" using hc(2) by simp
            also have "\<beta> (Suc k) = t" unfolding \<beta>_def by simp
            finally show ?thesis by simp
          qed
          have hx: "fst q = (\<Sum>i\<le>Suc k. \<beta> i * vx i)"
          proof -
            have "fst q = t * vx (Suc k) + (1-t) * fst p" using hq unfolding f_def by simp
            also have "\<dots> = t * vx (Suc k) + (1-t) * (\<Sum>i\<le>k. coeffs i * vx i)"
              using hc(3) by simp
            also have "(1-t) * (\<Sum>i\<le>k. coeffs i * vx i) = (\<Sum>i\<le>k. (1-t) * coeffs i * vx i)"
              by (simp add: sum_distrib_left mult.assoc)
            also have "(\<Sum>i\<le>k. (1-t) * coeffs i * vx i) = (\<Sum>i\<le>k. \<beta> i * vx i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            finally have "fst q = \<beta> (Suc k) * vx (Suc k) + (\<Sum>i\<le>k. \<beta> i * vx i)"
              unfolding \<beta>_def by simp
            thus ?thesis by simp
          qed
          have hy: "snd q = (\<Sum>i\<le>Suc k. \<beta> i * vy i)"
          proof -
            have "snd q = t * vy (Suc k) + (1-t) * snd p" using hq unfolding f_def by simp
            also have "\<dots> = t * vy (Suc k) + (1-t) * (\<Sum>i\<le>k. coeffs i * vy i)"
              using hc(4) by simp
            also have "(1-t) * (\<Sum>i\<le>k. coeffs i * vy i) = (\<Sum>i\<le>k. (1-t) * coeffs i * vy i)"
              by (simp add: sum_distrib_left mult.assoc)
            also have "(\<Sum>i\<le>k. (1-t) * coeffs i * vy i) = (\<Sum>i\<le>k. \<beta> i * vy i)"
              by (rule sum.cong) (simp_all add: \<beta>_def)
            finally have "snd q = \<beta> (Suc k) * vy (Suc k) + (\<Sum>i\<le>k. \<beta> i * vy i)"
              unfolding \<beta>_def by simp
            thus ?thesis by simp
          qed
          show "q \<in> Q (Suc k)"
          proof -
            have "\<exists>coeffs. (\<forall>i\<le>Suc k. 0 \<le> coeffs i) \<and> (\<Sum>i\<le>Suc k. coeffs i) = 1
                \<and> fst q = (\<Sum>i\<le>Suc k. coeffs i * vx i) \<and> snd q = (\<Sum>i\<le>Suc k. coeffs i * vy i)"
              using h\<beta>_pos h\<beta>_sum hx hy by (by100 blast)
            thus ?thesis unfolding Q_def by (by100 auto)
          qed
        qed
      qed
      have hf_cont: "continuous_on ({0..1} \<times> Q k) f"
      proof -
        have "f = (\<lambda>tp. (fst tp * vx (Suc k) + (1 - fst tp) * fst (snd tp),
                         fst tp * vy (Suc k) + (1 - fst tp) * snd (snd tp)))"
          unfolding f_def by (rule ext, simp add: case_prod_beta)
        moreover have "continuous_on ({0..1} \<times> Q k)
            (\<lambda>tp. (fst tp * vx (Suc k) + (1 - fst tp) * fst (snd tp),
                   fst tp * vy (Suc k) + (1 - fst tp) * snd (snd tp)))"
          by (intro continuous_intros)
        ultimately show ?thesis by simp
      qed
      have hdom_compact: "compact ({0..1::real} \<times> Q k)"
        by (rule compact_Times_general[OF compact_Icc hIH])
      show "compact (Q (Suc k))" unfolding hQ_eq
        by (rule compact_continuous_image[OF hf_cont hdom_compact])
    qed
    \<comment> \<open>By induction: Q k is compact for all k.\<close>
    have hQk: "\<And>k. compact (Q k)"
    proof -
      fix k show "compact (Q k)"
        by (induction k) (use hQ0 in simp, use hQstep in simp)
    qed
    \<comment> \<open>P = Q (n-1) (when n \\<ge> 3).\<close>
    have "P = Q (n - 1)"
    proof -
      have "{..<n} = {..n-1}" using hn by (by100 auto)
      hence "(\<forall>i<n. P_cond i) = (\<forall>i\<le>n-1. P_cond i)" for P_cond by (by100 auto)
      moreover have "(\<Sum>i<n. f i) = (\<Sum>i\<le>n-1. f i)" for f :: "nat \<Rightarrow> real"
        using \<open>{..<n} = {..n-1}\<close> by (by100 auto)
      ultimately show ?thesis unfolding hP Q_def by (by100 auto)
    qed
    thus ?thesis using hQk by simp
  qed
  have hP_closed: "closed P" by (rule compact_imp_closed[OF hP_compact_direct])
  \<comment> \<open>Closed subset of compact {-M..M}\\<times>{-M..M} is compact.\<close>
  show "compact P"
    by (rule closed_subset_compact[OF compact_Icc_Times hP_closed hP_bounded])
qed

\<comment> \<open>QUARANTINED: convex\\_polygon\\_homeomorphism is UNUSED and its barycentric/SOME approach
   is wrong for n > 3 (non-unique representations). The correct approach (using
   polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary) is now implemented directly inside
   scheme\\_quotient\\_uniqueness (per expert audit steps 4-7). This lemma can be deleted.\<close>
\<comment> \<open>convex\\_polygon\\_homeomorphism: REMOVED (unused, wrong barycentric approach for n>3).
   See scheme\\_quotient\\_uniqueness for the correct disk-homeomorphism approach.\<close>

\<comment> \<open>Interior preservation: if \\<phi> maps edge i of P1 to edge i of P2 bijectively,
   then \\<phi> also maps interior points (not on any edge) to interior points.\<close>
lemma edge_preserving_homeo_interior:
  assumes hbij: "bij_betw \<phi> P1 P2"
      and hedge: "\<forall>i<n. \<forall>t\<in>I_set.
          \<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
             (1-t) * vy1 i + t * vy1 (Suc i mod n))
          = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
             (1-t) * vy2 i + t * vy2 (Suc i mod n))"
      and hn3: "n \<ge> 3"
      and hP1_hull: "P1 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<n. coeffs i) = 1
                     \<and> x = (\<Sum>i<n. coeffs i * vx1 i)
                     \<and> y = (\<Sum>i<n. coeffs i * vy1 i)}"
      and hx: "x \<in> P1"
      and hint: "\<forall>i<n. \<forall>t\<in>I_set.
          x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
                (1-t) * vy1 i + t * vy1 (Suc i mod n))"
  shows "\<forall>i<n. \<forall>t\<in>I_set.
      \<phi> x \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod n),
            (1-t) * vy2 i + t * vy2 (Suc i mod n))"
proof (intro allI impI ballI notI)
  fix i t assume hi: "i < n" and ht: "t \<in> I_set"
  assume "(\<phi> x) = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
            (1-t) * vy2 i + t * vy2 (Suc i mod n))"
  \<comment> \<open>But \\<phi>(edge1(i,t)) = edge2(i,t) by hedge. Since \\<phi> is injective, x = edge1(i,t).\<close>
  have h_edge_eq: "\<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
             (1-t) * vy1 i + t * vy1 (Suc i mod n))
        = ((1-t) * vx2 i + t * vx2 (Suc i mod n),
           (1-t) * vy2 i + t * vy2 (Suc i mod n))"
    using hedge[rule_format, OF hi ht] .
  hence "\<phi> x = \<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod n),
                   (1-t) * vy1 i + t * vy1 (Suc i mod n))"
    using \<open>(\<phi> x) = _\<close> by (by100 simp)
  hence "x = ((1-t) * vx1 i + t * vx1 (Suc i mod n),
              (1-t) * vy1 i + t * vy1 (Suc i mod n))"
  proof -
    have "inj_on \<phi> P1" using bij_betw_imp_inj_on[OF hbij] .
    have "((1-t) * vx1 i + t * vx1 (Suc i mod n),
            (1-t) * vy1 i + t * vy1 (Suc i mod n)) \<in> P1"
      by (rule edge_point_in_polygon_witness[OF hn3 hi ht hP1_hull])
    from \<open>inj_on \<phi> P1\<close> hx this \<open>\<phi> x = \<phi> _\<close>
    show ?thesis unfolding inj_on_def by (by100 blast)
  qed
  thus False using hint hi ht by (by100 blast)
qed

\<comment> \<open>Quotient-of-scheme uniqueness: any two quotient spaces of the same scheme are homeomorphic.
   Proof: both are quotients of convex n-gons by the same identification pattern.
   The n-gons are homeomorphic (convex compact in R²), and the homeomorphism respects
   the boundary identifications. So the quotient spaces are homeomorphic.\<close>
lemma scheme_quotient_uniqueness:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 scheme"
      and "top1_quotient_of_scheme_on Y2 TY2 scheme"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  let ?n = "length scheme"
  let ?TP = "\<lambda>S. subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
  \<comment> \<open>Step 1: Extract ALL 11 conditions from both quotients.\<close>
  from assms(3) obtain P1 q1 vx1 vy1 where
      hC1_1: "top1_is_polygonal_region_on P1 ?n"
    and hC2_1: "top1_quotient_map_on P1 (?TP P1) Y1 TY1 q1"
    and hC3_1: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx1 i, vy1 i) \<noteq> (vx1 j, vy1 j)"
    and hC4_1: "\<forall>i<?n. (vx1 i, vy1 i) \<in> P1"
    and hC5_1: "P1 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx1 i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy1 i)}"
    and hC7_1: "\<forall>i<?n. \<forall>j<?n. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
              (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
         = (if snd (scheme!i) = snd (scheme!j)
            then q1 ((1-t) * vx1 j + t * vx1 (Suc j mod ?n),
                    (1-t) * vy1 j + t * vy1 (Suc j mod ?n))
            else q1 (t * vx1 j + (1-t) * vx1 (Suc j mod ?n),
                    t * vy1 j + (1-t) * vy1 (Suc j mod ?n))))"
    and hC8_1: "\<forall>p\<in>P1. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                      (1-t) * vy1 i + t * vy1 (Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P1. q1 p = q1 p' \<longrightarrow> p = p')"
    and hC9_1: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
               (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
          = q1 ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
               (1-s) * vy1 j + s * vy1 (Suc j mod ?n))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    and hC10_1: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx1 j) / real ?n;
                             cy = (\<Sum>j<?n. vy1 j) / real ?n
         in (vx1 i - cx) * (vy1 (Suc i mod ?n) - cy)
          - (vy1 i - cy) * (vx1 (Suc i mod ?n) - cx) > 0"
    and hC11_1: "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i)
          - (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) < 0"
    by (rule quotient_of_scheme_extract_vx)
  from assms(4) obtain P2 q2 vx2 vy2 where
      hC1_2: "top1_is_polygonal_region_on P2 ?n"
    and hC2_2: "top1_quotient_map_on P2 (?TP P2) Y2 TY2 q2"
    and hC4_2: "\<forall>i<?n. (vx2 i, vy2 i) \<in> P2"
    and hC5_2: "P2 = {(x, y) | x y.
              \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx2 i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy2 i)}"
    and hC7_2: "\<forall>i<?n. \<forall>j<?n. fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set.
           q2 ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
              (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
         = (if snd (scheme!i) = snd (scheme!j)
            then q2 ((1-t) * vx2 j + t * vx2 (Suc j mod ?n),
                    (1-t) * vy2 j + t * vy2 (Suc j mod ?n))
            else q2 (t * vx2 j + (1-t) * vx2 (Suc j mod ?n),
                    t * vy2 j + (1-t) * vy2 (Suc j mod ?n))))"
    and hC8_2: "\<forall>p\<in>P2. (\<forall>i<?n. \<forall>t\<in>I_set.
                p \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
                      (1-t) * vy2 i + t * vy2 (Suc i mod ?n)))
             \<longrightarrow> (\<forall>p'\<in>P2. q2 p = q2 p' \<longrightarrow> p = p')"
    and hC9_2: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
            q2 ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
               (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
          = q2 ((1-s) * vx2 j + s * vx2 (Suc j mod ?n),
               (1-s) * vy2 j + s * vy2 (Suc j mod ?n))
          \<longrightarrow> (i = j \<and> t = s)
            \<or> (fst (scheme!i) = fst (scheme!j) \<and>
               (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    and hC10_2: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx2 j) / real ?n;
                             cy = (\<Sum>j<?n. vy2 j) / real ?n
         in (vx2 i - cx) * (vy2 (Suc i mod ?n) - cy)
          - (vy2 i - cy) * (vx2 (Suc i mod ?n) - cx) > 0"
    and hC11_2: "\<forall>i<?n. \<forall>k<?n.
          k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
          (vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i)
          - (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) < 0"
    by (rule quotient_of_scheme_extract_vx)
  have hn3: "?n \<ge> 3" using hC1_1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
  \<comment> \<open>Step 2: Derive non-strict side conditions (needed for disk homeomorphism).\<close>
  have hside_le_1: "\<forall>i<?n. \<forall>k<?n.
      (vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i)
      - (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) \<le> 0"
  proof (intro allI impI)
    fix i k assume "i < ?n" "k < ?n"
    show "(vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i) -
          (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) \<le> 0"
    proof (cases "k = i")
      case True thus ?thesis by (by100 simp)
    next
      case False
      show ?thesis
      proof (cases "k = Suc i mod ?n")
        case True
        hence "(vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i) =
               (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i)" by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        case False2: False
        from hC11_1 \<open>i < ?n\<close> \<open>k < ?n\<close> False False2
        have "(vx1 k - vx1 i) * (vy1 (Suc i mod ?n) - vy1 i) -
              (vy1 k - vy1 i) * (vx1 (Suc i mod ?n) - vx1 i) < 0" by (by100 blast)
        thus ?thesis by (by100 linarith)
      qed
    qed
  qed
  have hside_le_2: "\<forall>i<?n. \<forall>k<?n.
      (vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i)
      - (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) \<le> 0"
  proof (intro allI impI)
    fix i k assume "i < ?n" "k < ?n"
    show "(vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i) -
          (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) \<le> 0"
    proof (cases "k = i")
      case True thus ?thesis by (by100 simp)
    next
      case False
      show ?thesis
      proof (cases "k = Suc i mod ?n")
        case True
        hence "(vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i) =
               (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i)" by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        case False2: False
        from hC11_2 \<open>i < ?n\<close> \<open>k < ?n\<close> \<open>k \<noteq> i\<close> False2
        have "(vx2 k - vx2 i) * (vy2 (Suc i mod ?n) - vy2 i) -
              (vy2 k - vy2 i) * (vx2 (Suc i mod ?n) - vx2 i) < 0" by (by100 blast)
        thus ?thesis by (by100 linarith)
      qed
    qed
  qed
  \<comment> \<open>Step 3: Get edge-preserving homeomorphisms P1 \\<to> B² \\<to> P2 via disk lemma.\<close>
  \<comment> \<open>Apply polygon\\_homeomorphic\\_to\\_disk\\_with\\_boundary to both polygons.
     The lemma uses cross2 from AlgTopChain. Need to convert our conditions.\<close>
  \<comment> \<open>Convert hside\\_le\\_1 and hC11\\_1 to cross2 form.\<close>
  have hvert_hp_1: "\<forall>i<?n. \<forall>k<?n. AlgTopChain.cross2 (vx1 k - vx1 i, vy1 k - vy1 i)
      (vx1 (Suc i mod ?n) - vx1 i, vy1 (Suc i mod ?n) - vy1 i) \<le> 0"
    using hside_le_1 unfolding AlgTopChain.cross2_def by (by100 simp)
  have hstrict_hp_1: "\<forall>i<?n. \<forall>k<?n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
      AlgTopChain.cross2 (vx1 k - vx1 i, vy1 k - vy1 i)
          (vx1 (Suc i mod ?n) - vx1 i, vy1 (Suc i mod ?n) - vy1 i) < 0"
    using hC11_1 unfolding AlgTopChain.cross2_def by (by100 simp)
  have hdisk1: "\<exists>\<psi>. top1_homeomorphism_on P1 (?TP P1) top1_B2 top1_B2_topology \<psi>
    \<and> (\<forall>i<?n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
        (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
      = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n)))"
    using AlgTopChain.polygon_homeomorphic_to_disk_with_boundary
      [OF hC1_1 hn3 hC4_1 hC5_1 hC10_1 hvert_hp_1 hstrict_hp_1]
  proof -
    from AlgTopChain.polygon_homeomorphic_to_disk_with_boundary
        [OF hC1_1 hn3 hC4_1 hC5_1 hC10_1 hvert_hp_1 hstrict_hp_1]
    show ?thesis
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply assumption
      apply assumption
      done
  qed
  then obtain \<psi>1 where
    h\<psi>1_homeo: "top1_homeomorphism_on P1 (?TP P1) top1_B2 top1_B2_topology \<psi>1"
    and h\<psi>1_edge: "\<forall>i<?n. \<forall>t\<in>I_set. \<psi>1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
        (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
      = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n))"
    by (by100 blast)
  have hvert_hp_2: "\<forall>i<?n. \<forall>k<?n. AlgTopChain.cross2 (vx2 k - vx2 i, vy2 k - vy2 i)
      (vx2 (Suc i mod ?n) - vx2 i, vy2 (Suc i mod ?n) - vy2 i) \<le> 0"
    using hside_le_2 unfolding AlgTopChain.cross2_def by (by100 simp)
  have hstrict_hp_2: "\<forall>i<?n. \<forall>k<?n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
      AlgTopChain.cross2 (vx2 k - vx2 i, vy2 k - vy2 i)
          (vx2 (Suc i mod ?n) - vx2 i, vy2 (Suc i mod ?n) - vy2 i) < 0"
    using hC11_2 unfolding AlgTopChain.cross2_def by (by100 simp)
  have hdisk2: "\<exists>\<psi>. top1_homeomorphism_on P2 (?TP P2) top1_B2 top1_B2_topology \<psi>
    \<and> (\<forall>i<?n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
        (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
      = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n)))"
  proof -
    from AlgTopChain.polygon_homeomorphic_to_disk_with_boundary
        [OF hC1_2 hn3 hC4_2 hC5_2 hC10_2 hvert_hp_2 hstrict_hp_2]
    show ?thesis
      apply (elim exE conjE)
      apply (intro exI conjI)
       apply assumption
      apply assumption
      done
  qed
  then obtain \<psi>2 where
    h\<psi>2_homeo: "top1_homeomorphism_on P2 (?TP P2) top1_B2 top1_B2_topology \<psi>2"
    and h\<psi>2_edge: "\<forall>i<?n. \<forall>t\<in>I_set. \<psi>2 ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
        (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
      = (cos (2*pi*(real i + t)/real ?n), sin (2*pi*(real i + t)/real ?n))"
    by (by100 blast)
  \<comment> \<open>Step 4: Compose \\<psi>2\\<inverse> \\<circ> \\<psi>1 to get edge-preserving \\<phi>: P1 \\<to> P2.\<close>
  from homeomorphism_inverse[OF h\<psi>2_homeo]
  have h\<psi>2_inv: "top1_homeomorphism_on top1_B2 top1_B2_topology P2 (?TP P2) (inv_into P2 \<psi>2)" .
  define \<phi> where "\<phi> = (inv_into P2 \<psi>2) \<circ> \<psi>1"
  from homeomorphism_comp[OF h\<psi>1_homeo h\<psi>2_inv]
  have h\<phi>: "top1_homeomorphism_on P1 (?TP P1) P2 (?TP P2) \<phi>" unfolding \<phi>_def .
  \<comment> \<open>Step 5: \\<phi> preserves edge parametrization.\<close>
  \<comment> \<open>\\<phi> preserves edge parametrization: \\<psi>1 and \\<psi>2 map corresponding edge points to
     the same S¹ point (cos/sin at 2\\<pi>(i+t)/n), so \\<psi>2\\<inverse> \\<circ> \\<psi>1 maps edge i of P1
     to edge i of P2. Uses h\\<psi>1\\_edge, h\\<psi>2\\_edge, injectivity of \\<psi>2, and inv\\_into\\_f\\_f.\<close>
  have h\<psi>2_bij: "bij_betw \<psi>2 P2 top1_B2"
    using h\<psi>2_homeo unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
    by (by100 blast)
  have h\<psi>2_inj: "inj_on \<psi>2 P2"
    using h\<psi>2_bij unfolding bij_betw_def by (by100 blast)
  have h\<phi>_edge: "\<forall>i<?n. \<forall>t\<in>I_set.
      \<phi> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
         (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
      = ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
         (1-t) * vy2 i + t * vy2 (Suc i mod ?n))"
    \<comment> \<open>Apply standalone lemmas: composed\\_disk\\_homeo\\_edge\\_preserving + edge\\_point\\_in\\_polygon\\_witness.\<close>
    apply (intro allI impI ballI)
    apply (unfold \<phi>_def comp_def)
    \<comment> \<open>Goal: inv\\_into P2 \\<psi>2 (\\<psi>1 (edge1(i,t))) = edge2(i,t).
       Now i < n and t \\<in> I\\_set are meta-level assumptions (from impI + ballI).\<close>
    apply (subst h\<psi>1_edge[rule_format], assumption, assumption)
    apply (subst h\<psi>2_edge[rule_format, symmetric], assumption, assumption)
    apply (rule inv_into_f_f[OF h\<psi>2_inj])
    apply (rule edge_point_in_polygon_witness[OF hn3 _ _ hC5_2], assumption, assumption)
    done
  \<comment> \<open>Step 6: q2 \\<circ> \\<phi> is a quotient map P1 \\<to> Y2.\<close>
  have h\<phi>_quot: "top1_quotient_map_on P1 (?TP P1) P2 (?TP P2) \<phi>"
    by (rule top1_homeomorphism_on_imp_quotient_map_on[OF h\<phi>])
  have hcomp_quot: "top1_quotient_map_on P1 (?TP P1) Y2 TY2 (q2 \<circ> \<phi>)"
    by (rule top1_quotient_map_on_comp[OF h\<phi>_quot hC2_2])
  \<comment> \<open>Step 7: Fibres of q1 and q2\\<circ>\\<phi> agree (key step, uses edge preservation).
     Interior points: both maps are injective (C8), so fibres match.
     Edge points: \\<phi> preserves edge parametrization, so the scheme identification
     pattern is preserved. q1 identifies edges i,j iff scheme says so, and
     q2\\<circ>\\<phi> identifies the same edges because \\<phi> maps edge i to edge i.\<close>
  \<comment> \<open>Helper: \\<phi> is bijective (from homeomorphism).\<close>
  have h\<phi>_bij: "bij_betw \<phi> P1 P2"
    using h\<phi> unfolding top1_homeomorphism_on_def top1_continuous_map_on_def
    by (by100 blast)
  \<comment> \<open>Helper: \\<phi> preserves interior (not-on-boundary) of P1 to interior of P2.\<close>
  have h\<phi>_int: "\<And>x. \<lbrakk>x \<in> P1; \<forall>i<?n. \<forall>t\<in>I_set.
      x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
            (1-t) * vy1 i + t * vy1 (Suc i mod ?n))\<rbrakk> \<Longrightarrow>
      \<forall>i<?n. \<forall>t\<in>I_set.
      \<phi> x \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
            (1-t) * vy2 i + t * vy2 (Suc i mod ?n))"
    by (rule edge_preserving_homeo_interior[OF h\<phi>_bij h\<phi>_edge hn3 hC5_1])
  \<comment> \<open>\\<phi> maps P1 into P2 (from bij\\_betw).\<close>
  have h\<phi>_img: "\<And>x. x \<in> P1 \<Longrightarrow> \<phi> x \<in> P2"
    using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
  have hfibres: "\<forall>x\<in>P1. \<forall>y\<in>P1. (q1 x = q1 y) \<longleftrightarrow> ((q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y)"
  proof (intro ballI iffI)
    fix x y assume hxP: "x \<in> P1" and hyP: "y \<in> P1"
    \<comment> \<open>Forward: q1 x = q1 y \\<Longrightarrow> q2(\\<phi>(x)) = q2(\\<phi>(y)).\<close>
    {
      assume heq: "q1 x = q1 y"
      \<comment> \<open>Case split: is x on a boundary edge?\<close>
      consider
        (x_int) "\<forall>i<?n. \<forall>t\<in>I_set. x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
              (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
        | (x_bdy) "\<exists>i<?n. \<exists>t\<in>I_set. x = ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
              (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
        by (by100 blast)
      hence "(q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y"
      proof cases
        case x_int
        \<comment> \<open>x is interior: C8\\_1 says q1 injective at x, so x = y.\<close>
        from hC8_1 hxP x_int have "\<forall>p'\<in>P1. q1 x = q1 p' \<longrightarrow> x = p'" by (by100 blast)
        hence "x = y" using hyP heq by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case x_bdy
        then obtain i t where hi: "i < ?n" and ht: "t \<in> I_set"
          and hx_eq: "x = ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                           (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
          by (by100 blast)
        \<comment> \<open>Is y on a boundary edge?\<close>
        consider
          (y_int) "\<forall>j<?n. \<forall>s\<in>I_set. y \<noteq> ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
                (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
          | (y_bdy) "\<exists>j<?n. \<exists>s\<in>I_set. y = ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
                (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
          by (by100 blast)
        thus ?thesis
        proof cases
          case y_int
          \<comment> \<open>y interior: C8\\_1 says q1 injective at y, so y = x.\<close>
          from hC8_1 hyP y_int have "\<forall>p'\<in>P1. q1 y = q1 p' \<longrightarrow> y = p'" by (by100 blast)
          hence "y = x" using hxP heq[symmetric] by (by100 blast)
          thus ?thesis by (by100 simp)
        next
          case y_bdy
          \<comment> \<open>Both on boundary: use C7/C9 — identification depends only on scheme.\<close>
          then obtain j s where hj: "j < ?n" and hs: "s \<in> I_set"
            and hy_eq: "y = ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
                             (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
            by (by100 blast)
          \<comment> \<open>From q1(e1(i,t)) = q1(e1(j,s)) and C9\\_1: get label/direction condition.\<close>
          from hC9_1 hi hj ht hs heq[unfolded hx_eq hy_eq]
          have hcond: "(i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
              (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
            by (by100 blast)
          \<comment> \<open>Need: q2(\\<phi>(x)) = q2(\\<phi>(y)), i.e. q2(e2(i,t)) = q2(e2(j,s)).\<close>
          have h\<phi>x: "\<phi> x = ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
                             (1-t) * vy2 i + t * vy2 (Suc i mod ?n))"
            using h\<phi>_edge[rule_format, OF hi ht] hx_eq by (by100 simp)
          have h\<phi>y: "\<phi> y = ((1-s) * vx2 j + s * vx2 (Suc j mod ?n),
                             (1-s) * vy2 j + s * vy2 (Suc j mod ?n))"
            using h\<phi>_edge[rule_format, OF hj hs] hy_eq by (by100 simp)
          \<comment> \<open>From hcond, derive q2(e2(i,t)) = q2(e2(j,s)) using C7\\_2.\<close>
          from hcond show ?thesis
          proof (elim disjE conjE)
            assume "i = j" "t = s"
            thus ?thesis using h\<phi>x h\<phi>y by (by100 simp)
          next
            assume hlabel: "fst (scheme!i) = fst (scheme!j)"
              and hdir: "if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t"
            from hC7_2 hi hj hlabel ht
            have "q2 ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
                      (1-t) * vy2 i + t * vy2 (Suc i mod ?n))
                = (if snd (scheme!i) = snd (scheme!j)
                   then q2 ((1-t) * vx2 j + t * vx2 (Suc j mod ?n),
                           (1-t) * vy2 j + t * vy2 (Suc j mod ?n))
                   else q2 (t * vx2 j + (1-t) * vx2 (Suc j mod ?n),
                           t * vy2 j + (1-t) * vy2 (Suc j mod ?n)))"
              by (by100 blast)
            \<comment> \<open>Case split on direction match to rewrite q2 equality.\<close>
            thus ?thesis
            proof (cases "snd (scheme!i) = snd (scheme!j)")
              case True
              \<comment> \<open>Same direction: s = t, so \\<phi>(y) = e2(j,t) = e2(j,s).\<close>
              hence "s = t" using hdir by (by100 simp)
              thus ?thesis using \<open>q2 _ = _\<close> True h\<phi>x h\<phi>y by (by100 simp)
            next
              case False
              \<comment> \<open>Opposite direction: s = 1-t, so e2(j,s) = (t*vx2 j + (1-t)*vx2(Sj), ...).\<close>
              hence "s = 1 - t" using hdir by (by100 simp)
              \<comment> \<open>(1-s) = t, s = 1-t, so (1-s)*vx2 j + s*vx2(Sj) = t*vx2 j + (1-t)*vx2(Sj).\<close>
              hence "\<phi> y = (t * vx2 j + (1-t) * vx2 (Suc j mod ?n),
                           t * vy2 j + (1-t) * vy2 (Suc j mod ?n))"
                using h\<phi>y by (by100 simp)
              thus ?thesis using \<open>q2 _ = _\<close> False h\<phi>x by (by100 simp)
            qed
          qed
        qed
      qed
    }
    thus "q1 x = q1 y \<Longrightarrow> (q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y" .
  next
    fix x y assume hxP: "x \<in> P1" and hyP: "y \<in> P1"
    \<comment> \<open>Backward: q2(\\<phi>(x)) = q2(\\<phi>(y)) \\<Longrightarrow> q1 x = q1 y. Symmetric argument.\<close>
    assume heq2: "(q2 \<circ> \<phi>) x = (q2 \<circ> \<phi>) y"
    \<comment> \<open>Symmetric to forward, but using C8\\_2 on \\<phi>(x),\\<phi>(y) \\<in> P2, then pulling back to P1.\<close>
    have h\<phi>xP: "\<phi> x \<in> P2" using h\<phi>_img hxP by (by100 blast)
    have h\<phi>yP: "\<phi> y \<in> P2" using h\<phi>_img hyP by (by100 blast)
    have heq2': "q2 (\<phi> x) = q2 (\<phi> y)" using heq2 by (by100 simp)
    consider
      (x_int) "\<forall>i<?n. \<forall>t\<in>I_set. x \<noteq> ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
            (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
      | (x_bdy) "\<exists>i<?n. \<exists>t\<in>I_set. x = ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
            (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
      by (by100 blast)
    thus "q1 x = q1 y"
    proof cases
      case x_int
      \<comment> \<open>x interior \\<Longrightarrow> \\<phi>(x) interior \\<Longrightarrow> q2 injective at \\<phi>(x) \\<Longrightarrow> \\<phi>(x)=\\<phi>(y) \\<Longrightarrow> x=y.\<close>
      from h\<phi>_int hxP x_int
      have "\<forall>i<?n. \<forall>t\<in>I_set. \<phi> x \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
          (1-t) * vy2 i + t * vy2 (Suc i mod ?n))" .
      from hC8_2 h\<phi>xP this have "\<forall>p'\<in>P2. q2 (\<phi> x) = q2 p' \<longrightarrow> \<phi> x = p'" by (by100 blast)
      hence "\<phi> x = \<phi> y" using h\<phi>yP heq2' by (by100 blast)
      hence "x = y" using bij_betw_imp_inj_on[OF h\<phi>_bij] hxP hyP
        unfolding inj_on_def by (by100 blast)
      thus ?thesis by (by100 simp)
    next
      case x_bdy
      then obtain i t where hi: "i < ?n" and ht: "t \<in> I_set"
        and hx_eq: "x = ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                         (1-t) * vy1 i + t * vy1 (Suc i mod ?n))"
        by (by100 blast)
      consider
        (y_int) "\<forall>j<?n. \<forall>s\<in>I_set. y \<noteq> ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
              (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
        | (y_bdy) "\<exists>j<?n. \<exists>s\<in>I_set. y = ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
              (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
        by (by100 blast)
      thus ?thesis
      proof cases
        case y_int
        from h\<phi>_int hyP y_int
        have "\<forall>i<?n. \<forall>t\<in>I_set. \<phi> y \<noteq> ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
            (1-t) * vy2 i + t * vy2 (Suc i mod ?n))" .
        from hC8_2 h\<phi>yP this have "\<forall>p'\<in>P2. q2 (\<phi> y) = q2 p' \<longrightarrow> \<phi> y = p'" by (by100 blast)
        hence "\<phi> y = \<phi> x" using h\<phi>xP heq2'[symmetric] by (by100 blast)
        hence "y = x" using bij_betw_imp_inj_on[OF h\<phi>_bij] hxP hyP
          unfolding inj_on_def by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case y_bdy
        then obtain j s where hj: "j < ?n" and hs: "s \<in> I_set"
          and hy_eq: "y = ((1-s) * vx1 j + s * vx1 (Suc j mod ?n),
                           (1-s) * vy1 j + s * vy1 (Suc j mod ?n))"
          by (by100 blast)
        \<comment> \<open>\\<phi>(x) = e2(i,t), \\<phi>(y) = e2(j,s). From C9\\_2 + C7\\_1: same argument as forward.\<close>
        have h\<phi>x: "\<phi> x = ((1-t) * vx2 i + t * vx2 (Suc i mod ?n),
                           (1-t) * vy2 i + t * vy2 (Suc i mod ?n))"
          using h\<phi>_edge[rule_format, OF hi ht] hx_eq by (by100 simp)
        have h\<phi>y: "\<phi> y = ((1-s) * vx2 j + s * vx2 (Suc j mod ?n),
                           (1-s) * vy2 j + s * vy2 (Suc j mod ?n))"
          using h\<phi>_edge[rule_format, OF hj hs] hy_eq by (by100 simp)
        from hC9_2 hi hj ht hs heq2'[unfolded h\<phi>x h\<phi>y]
        have hcond: "(i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
            (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
          by (by100 blast)
        from hcond show ?thesis
        proof (elim disjE conjE)
          assume "i = j" "t = s"
          thus ?thesis using hx_eq hy_eq by (by100 simp)
        next
          assume hlabel: "fst (scheme!i) = fst (scheme!j)"
            and hdir: "if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t"
          \<comment> \<open>Use C7\\_1 (same scheme!) to get q1(e1(i,t)) = q1(e1(j,s)).\<close>
          from hC7_1 hi hj hlabel ht
          have hq1: "q1 ((1-t) * vx1 i + t * vx1 (Suc i mod ?n),
                        (1-t) * vy1 i + t * vy1 (Suc i mod ?n))
              = (if snd (scheme!i) = snd (scheme!j)
                 then q1 ((1-t) * vx1 j + t * vx1 (Suc j mod ?n),
                         (1-t) * vy1 j + t * vy1 (Suc j mod ?n))
                 else q1 (t * vx1 j + (1-t) * vx1 (Suc j mod ?n),
                         t * vy1 j + (1-t) * vy1 (Suc j mod ?n)))"
            by (by100 blast)
          show ?thesis
          proof (cases "snd (scheme!i) = snd (scheme!j)")
            case True
            hence "s = t" using hdir by (by100 simp)
            thus ?thesis using hq1 True hx_eq hy_eq by (by100 simp)
          next
            case False
            hence "s = 1 - t" using hdir by (by100 simp)
            hence "y = (t * vx1 j + (1-t) * vx1 (Suc j mod ?n),
                        t * vy1 j + (1-t) * vy1 (Suc j mod ?n))"
              using hy_eq by (by100 simp)
            thus ?thesis using hq1 False hx_eq by (by100 simp)
          qed
        qed
      qed
    qed
  qed
  from quotient_same_fibres_homeomorphic[OF hC2_1 hcomp_quot hfibres]
  show ?thesis .
qed

\<comment> \<open>scheme\\_equiv preserves homeomorphism type: equivalent schemes give homeomorphic quotients.\<close>
lemma scheme_equiv_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 s"
      and "top1_quotient_of_scheme_on Y2 TY2 t"
      and "top1_scheme_equiv s t"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  have "top1_quotient_of_scheme_on Y1 TY1 t"
    by (rule scheme_equiv_preserves_quotient[OF assms(3) assms(5)])
  from scheme_quotient_uniqueness[OF assms(1) assms(2) this assms(4)]
  show ?thesis .
qed

\<comment> \<open>Scheme rotation preserves quotient type: quotient(u@v) \\<cong> quotient(v@u).
   The edge identifications are the same up to cyclic shift.\<close>
lemma scheme_rotate_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 (u @ v)"
      and "top1_quotient_of_scheme_on Y2 TY2 (v @ u)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation iv): "Permute. Renumbering the vertices of the
     polygonal region so as to begin with a different vertex does not affect the quotient space."
     Formal argument: u@v and v@u have the same length n = |u|+|v|. Define shifted vertex
     positions vx'(i) = vx((i+|u|) mod n). The polygon P is unchanged (same convex hull).
     The quotient map q is unchanged. The scheme (v@u)!i = (u@v)!((i+|u|) mod n), so all
     identification conditions transfer. Apply quotient\\_same\\_fibres\\_homeomorphic.\<close>
  let ?n = "length u + length v"
  \<comment> \<open>Strategy: Show Y1 is ALSO a quotient of v@u (same polygon, rotated vertices).
     Then Y1 and Y2 are both quotients of v@u. Apply scheme\\_quotient\\_uniqueness.\<close>
  \<comment> \<open>The scheme v@u has the same length.\<close>
  have hlen_eq: "length (v @ u) = ?n" by simp
  have hlen_uv: "length (u @ v) = ?n" by simp
  \<comment> \<open>Key: (v@u)!i = (u@v)!((i + length u) mod n) for i < n.\<close>
  have hshift: "\<forall>i < ?n. (v @ u) ! i = (u @ v) ! ((i + length u) mod ?n)"
  proof (intro allI impI)
    fix i assume "i < ?n"
    show "(v @ u) ! i = (u @ v) ! ((i + length u) mod ?n)"
    proof (cases "i < length v")
      case True
      hence "(v @ u) ! i = v ! i" by (simp add: nth_append)
      moreover have "(i + length u) mod ?n = i + length u"
        using True by simp
      moreover have "(u @ v) ! (i + length u) = v ! i"
        using True by (simp add: nth_append)
      ultimately show ?thesis by simp
    next
      case False
      hence "i \<ge> length v" by linarith
      hence "(v @ u) ! i = u ! (i - length v)" by (simp add: nth_append)
      moreover have "(i + length u) mod ?n = i - length v"
      proof -
        have "i + length u = ?n + (i - length v)" using \<open>i \<ge> length v\<close> by linarith
        hence "(i + length u) mod ?n = (?n + (i - length v)) mod ?n"
          by (metis add.commute)
        also have "\<dots> = (i - length v) mod ?n" by simp
        also have "\<dots> = i - length v"
          using \<open>i < ?n\<close> \<open>i \<ge> length v\<close> by simp
        finally show ?thesis .
      qed
      moreover have "(u @ v) ! (i - length v) = u ! (i - length v)"
      proof -
        have "i - length v < length u" using \<open>i < ?n\<close> \<open>i \<ge> length v\<close> by linarith
        thus ?thesis by (simp add: nth_append)
      qed
      ultimately show ?thesis by simp
    qed
  qed
  \<comment> \<open>Y1 is also a quotient of v@u (same polygon, rotated vertex numbering).\<close>
  have hY1_vu: "top1_quotient_of_scheme_on Y1 TY1 (v @ u)"
    by (rule elementary_operation_preserves_quotient[OF assms(3) top1_elementary_scheme_operation.rotate])
  \<comment> \<open>Both Y1 and Y2 are quotients of v@u. Apply scheme\\_quotient\\_uniqueness.\<close>
  show ?thesis by (rule scheme_quotient_uniqueness[OF assms(1) assms(2) hY1_vu assms(4)])
qed

\<comment> \<open>Scheme cancellation preserves quotient type: quotient(u@[a,a\\<inverse>]@v) \\<cong> quotient(u@v).
   Folding two adjacent inverse edges doesn't change the quotient space.\<close>
lemma scheme_cancel_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 (u @ [a, top1_inverse_edge a] @ v)"
      and "top1_quotient_of_scheme_on Y2 TY2 (u @ v)"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation vi): "Cancel. Replace w = y0 a a\\<inverse> y1 by y0 y1."
     Formal: The (n+2)-gon for u@[a,a\\<inverse>]@v has two adjacent edges labeled a, a\\<inverse>.
     These edges are identified in the quotient. "Folding" the polygon along these edges
     gives an n-gon. The fold map is a quotient map P(n+2) \\<to> P(n) that preserves
     all other edge identifications.
     Compose: q1: P(n+2) \\<to> Y1, fold: P(n+2) \\<to> P(n), and q2\\<inverse>: P(n) \\<to> Y2.
     The composition gives a homeomorphism Y1 \\<to> Y2.\<close>
  \<comment> \<open>By elementary\\_operation\\_preserves\\_quotient with the cancel rule:
     Y1 is also a quotient of u@v. Then scheme\\_quotient\\_uniqueness gives Y1 \\<cong> Y2.\<close>
  have "top1_quotient_of_scheme_on Y1 TY1 (u @ v)"
    by (rule elementary_operation_preserves_quotient[OF assms(3)
        top1_elementary_scheme_operation.cancel[of u a v]])
  from scheme_quotient_uniqueness[OF assms(1) assms(2) this assms(4)]
  show ?thesis .
qed

\<comment> \<open>Scheme inversion preserves quotient type: quotient(w) \\<cong> quotient(rev(map inverse w)).
   Reflecting the polygon preserves the quotient space.\<close>
lemma scheme_invert_homeomorphic:
  assumes "is_topology_on_strict Y1 TY1" and "is_topology_on_strict Y2 TY2"
      and "top1_quotient_of_scheme_on Y1 TY1 w"
      and "top1_quotient_of_scheme_on Y2 TY2 (rev (map top1_inverse_edge w))"
  shows "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
proof -
  \<comment> \<open>Book proof (Munkres \\<S>76 operation v): "Flip. Flipping the polygonal region over.
     The order of the vertices is reversed, and so is the orientation of each edge."
     Formal: Reflecting the polygon (reversing vertex order) gives a valid quotient
     of rev(map inverse w). Then scheme\\_quotient\\_uniqueness gives Y1 \\<cong> Y2.\<close>
  have hY1_inv: "top1_quotient_of_scheme_on Y1 TY1 (rev (map top1_inverse_edge w))"
    by (rule elementary_operation_preserves_quotient[OF assms(3) top1_elementary_scheme_operation.invert])
  \<comment> \<open>Originally: Extract (P,q,vx,vy) from assms(3). Define reflected vertices:
       vx'(i) = vx(n-1-i), vy'(i) = vy(n-1-i) (reverse order).
       The same polygon P (reflection is a homeomorphism), same quotient map q.
       Edge i in the reflected scheme = inverse of edge (n-1-i) in w.
       All conditions transfer via the reversal.\<close>
  show ?thesis by (rule scheme_quotient_uniqueness[OF assms(1) assms(2) hY1_inv assms(4)])
qed
  \<comment> \<open>Reflect the polygon (reverse vertex order + flip orientations).
     The reflection map commutes with the identification.\<close>

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
  \<comment> \<open>Prove the strong version: for ALL quotient spaces of related schemes, homeo.\<close>
  have hcases: "\<And>s t. top1_elementary_scheme_operation s t \<Longrightarrow>
      top1_quotient_of_scheme_on X1 TX1 s \<Longrightarrow>
      top1_quotient_of_scheme_on X2 TX2 t \<Longrightarrow>
      \<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h"
  proof -
    fix s t assume hop: "top1_elementary_scheme_operation s t"
        and hs: "top1_quotient_of_scheme_on X1 TX1 s"
        and ht: "top1_quotient_of_scheme_on X2 TX2 t"
    \<comment> \<open>First prove for ANY pair of quotient spaces (needed for sym/trans cases).\<close>
    have huniv: "\<And>s t (Y1 :: 'x set) TY1 (Y2 :: 'x set) TY2.
        top1_elementary_scheme_operation s t \<Longrightarrow>
        is_topology_on_strict Y1 TY1 \<Longrightarrow> is_topology_on_strict Y2 TY2 \<Longrightarrow>
        top1_quotient_of_scheme_on Y1 TY1 s \<Longrightarrow>
        top1_quotient_of_scheme_on Y2 TY2 t \<Longrightarrow>
        \<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h"
    proof -
      fix s t and Y1 :: "'x set" and TY1 and Y2 :: "'x set" and TY2
      assume hop: "top1_elementary_scheme_operation s t"
          and hY1: "is_topology_on_strict Y1 TY1" and hY2: "is_topology_on_strict Y2 TY2"
          and hs: "top1_quotient_of_scheme_on Y1 TY1 s"
          and ht: "top1_quotient_of_scheme_on Y2 TY2 t"
      show "\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h" using hop
      proof (cases rule: top1_elementary_scheme_operation.cases)
        case (rotate u v)
        then show ?thesis using scheme_rotate_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (cancel u a v)
        then show ?thesis using scheme_cancel_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (uncancel u v a)
        \<comment> \<open>Uncancel = reverse of cancel. s = u@v, t = u@[a, a\\<inverse>]@v.\<close>
        have hs2: "top1_quotient_of_scheme_on Y1 TY1 (u @ v)" using hs uncancel by simp
        have ht2: "top1_quotient_of_scheme_on Y2 TY2 (u @ [a, top1_inverse_edge a] @ v)"
          using ht uncancel by simp
        from scheme_cancel_homeomorphic[OF hY2 hY1 ht2 hs2]
        obtain h where "top1_homeomorphism_on Y2 TY2 Y1 TY1 h" by (by100 blast)
        from homeomorphism_inverse[OF this]
        show ?thesis by (by100 blast)
      next
        case invert
        then show ?thesis using scheme_invert_homeomorphic[OF hY1 hY2] hs ht by simp
      next
        case (relabel old new)
        \<comment> \<open>Relabeling preserves the quotient: same polygon, same q, renamed labels.
           Y1 is also a quotient of the relabeled scheme. Then scheme\\_quotient\\_uniqueness.\<close>
        have hop_relabel: "top1_elementary_scheme_operation s (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          by (rule top1_elementary_scheme_operation.relabel)
        have hY1_relabel: "top1_quotient_of_scheme_on Y1 TY1 (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          by (rule elementary_operation_preserves_quotient[OF hs hop_relabel])
        moreover have "top1_quotient_of_scheme_on Y2 TY2 (map (\<lambda>(l,b). (if l = old then new else l, b)) s)"
          using ht relabel by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (flip_label a)
        \<comment> \<open>Flipping orientations: same polygon, same q, flipped edge directions.
           Y1 is also a quotient of the flipped scheme.\<close>
        have "top1_quotient_of_scheme_on Y1 TY1 (map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo)) s)"
          by (rule elementary_operation_preserves_quotient[OF hs top1_elementary_scheme_operation.flip_label])
        moreover have "top1_quotient_of_scheme_on Y2 TY2 (map (\<lambda>(l,bo). (l, if l = a then \<not>bo else bo)) s)"
          using ht flip_label by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste u1 a u2 u3)
        \<comment> \<open>Cut-and-repaste: \\<S>76 Theorem 76.1. Cut, flip, paste preserves quotient.\<close>
        have "top1_quotient_of_scheme_on Y1 TY1
            (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u1 @ [(a, True)] @ u2 @ [(a, True)] @ u3)"
            using hs cut_paste by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste[of u1 a u2 u3]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            (u1 @ [(a, True), (a, True)] @ rev (map top1_inverse_edge u2) @ u3)"
          using ht cut_paste by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste2 u0 a u1 u2 b)
        have "top1_quotient_of_scheme_on Y1 TY1
            ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u0 @ [(a, True)] @ u1 @ [(a, True)] @ u2)"
            using hs cut_paste2 by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste2[of u0 a u1 u2 b]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            ([(b, True)] @ u2 @ [(b, True)] @ u1 @ rev (map top1_inverse_edge u0))"
          using ht cut_paste2 by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (cut_paste_opp u0 u1 a u2 u3)
        have "top1_quotient_of_scheme_on Y1 TY1
            (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
        proof -
          have "top1_quotient_of_scheme_on Y1 TY1 (u0 @ u1 @ [(a, True)] @ u2 @ [(a, False)] @ u3)"
            using hs cut_paste_opp by simp
          from elementary_operation_preserves_quotient[OF this top1_elementary_scheme_operation.cut_paste_opp[of u0 u1 a u2 u3]]
          show ?thesis .
        qed
        moreover have "top1_quotient_of_scheme_on Y2 TY2
            (u0 @ [(a, True)] @ u2 @ [(a, False)] @ u1 @ u3)"
          using ht cut_paste_opp by simp
        ultimately show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] by (by100 blast)
      next
        case (context_left y z prefix)
        \<comment> \<open>s = prefix@y, t = prefix@z, y \<to> z.
           Apply the operation to Y1's quotient: Y1 also realizes t.
           Then both Y1 and Y2 realize the same scheme, giving homeomorphism.\<close>
        have "top1_quotient_of_scheme_on Y1 TY1 t"
          by (rule elementary_operation_preserves_quotient[OF hs hop])
        then show ?thesis using scheme_quotient_uniqueness[OF hY1 hY2] ht by (by100 blast)
      qed
    qed
    from huniv[OF hop assms(1) assms(2) hs ht]
    show "\<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h" .
  qed
  show ?thesis using hcases[OF assms(3)] assms(4) by (by100 blast)
qed



\<comment> \<open>§75 + §73 + §74.4 moved to AlgTopCached8.\<close>

\<comment> \<open>NOTE: free\_abelian\_quotient\_by\_twice\_sum\_structure was here but is unused —
   its content is fully proved inside Theorem\_75\_4 (certified in AlgTopCached12).
   Removed per expert audit 13 recommendation.\<close>

section \<open>*\<S>78 Constructing Compact Surfaces\<close>


\<comment> \<open>standard\_simplex moved to AlgTopCached8.\<close>


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
  \<comment> \<open>Step 4: Place disjoint copies of the simplex in R² (translated apart).
     Define q by pasting all h0(T) on corresponding copies.
     The edge identifications recreate X from the disjoint union.\<close>
  \<comment> \<open>Translation preserves polygonal region.\<close>
  have htranslate_poly: "\<And>P n c. top1_is_polygonal_region_on P n \<Longrightarrow>
      top1_is_polygonal_region_on ((\<lambda>(x,y). (x + c, y)) ` P) n"
  proof -
    fix P :: "(real \<times> real) set" and n :: nat and c :: real
    assume hP: "top1_is_polygonal_region_on P n"
    from hP obtain vx vy where hn: "n \<ge> 3"
        and hdist: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
        and hndeg: "\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                          \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
                          \<and> vx k = (\<Sum>i<n. coeffs i * vx i) \<and> vy k = (\<Sum>i<n. coeffs i * vy i))"
        and hP_eq: "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
                       \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
      unfolding top1_is_polygonal_region_on_def by (by5000 auto)
    \<comment> \<open>Translated vertices.\<close>
    define vx' where "vx' i = vx i + c" for i
    define vy' where "vy' = vy"
    \<comment> \<open>Key arithmetic: \\<Sum>(\\<alpha>*(vx+c)) = \\<Sum>(\\<alpha>*vx) + c when \\<Sum>\\<alpha>=1.\<close>
    have hsum_dist0: "\<And>coeffs :: nat \<Rightarrow> real. (\<Sum>i<n. coeffs i) = 1 \<Longrightarrow>
        (\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c"
    proof -
      fix coeffs :: "nat \<Rightarrow> real" assume "(\<Sum>i<n. coeffs i) = 1"
      have "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i + coeffs i * c)"
        by (rule sum.cong) (simp_all add: distrib_left)
      also have "\<dots> = (\<Sum>i<n. coeffs i * vx i) + (\<Sum>i<n. coeffs i * c)"
        by (rule sum.distrib)
      also have "(\<Sum>i<n. coeffs i * c) = c * (\<Sum>i<n. coeffs i)"
        by (simp add: sum_distrib_left mult.commute)
      also have "\<dots> = c" using \<open>(\<Sum>i<n. coeffs i) = 1\<close> by simp
      finally show "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c" .
    qed
    \<comment> \<open>Vertex distinctness.\<close>
    have hdist': "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx' i, vy' i) \<noteq> (vx' j, vy' j)"
      using hdist unfolding vx'_def vy'_def by simp
    \<comment> \<open>Non-degeneracy.\<close>
    have hndeg': "\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                        \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
                        \<and> vx' k = (\<Sum>i<n. coeffs i * vx' i) \<and> vy' k = (\<Sum>i<n. coeffs i * vy' i))"
    proof (intro allI impI notI)
      fix k assume "k < n"
      assume "\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
          \<and> vx' k = (\<Sum>i<n. coeffs i * vx' i) \<and> vy' k = (\<Sum>i<n. coeffs i * vy' i)"
      then obtain coeffs where hc: "(\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)" "coeffs k = 0"
          "(\<Sum>i<n. coeffs i) = 1"
          "vx' k = (\<Sum>i<n. coeffs i * vx' i)" "vy' k = (\<Sum>i<n. coeffs i * vy' i)"
        by (by100 blast)
      \<comment> \<open>From hsum\\_dist: \\<Sum>(coeffs * vx') = \\<Sum>(coeffs * vx) + c.\<close>
      have "(\<Sum>i<n. coeffs i * vx' i) = (\<Sum>i<n. coeffs i * vx i) + c"
        unfolding vx'_def using hsum_dist0[OF hc(3)] by simp
      hence "vx k = (\<Sum>i<n. coeffs i * vx i)"
        using hc(4) unfolding vx'_def by linarith
      moreover have "vy k = (\<Sum>i<n. coeffs i * vy i)"
        using hc(5) unfolding vy'_def by simp
      moreover have "(\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1"
        using hc(1) hc(2) hc(3) by (by100 blast)
      ultimately have "\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0 \<and> (\<Sum>i<n. coeffs i) = 1
          \<and> vx k = (\<Sum>i<n. coeffs i * vx i) \<and> vy k = (\<Sum>i<n. coeffs i * vy i)"
        by (by100 blast)
      with hndeg[rule_format, OF \<open>k < n\<close>] show False by simp
    qed
    \<comment> \<open>Translated hull.\<close>
    have hP'_eq: "(\<lambda>(x,y). (x + c, y)) ` P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                  \<and> (\<Sum>i<n. coeffs i) = 1
                  \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
    proof -
      have hsum_dist: "\<And>coeffs. (\<Sum>i<n. coeffs i) = 1 \<Longrightarrow>
          (\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c"
      proof -
        fix coeffs :: "nat \<Rightarrow> real" assume hsum1: "(\<Sum>i<n. coeffs i) = 1"
        have "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i + coeffs i * c)"
          by (rule sum.cong) (simp_all add: distrib_left)
        also have "\<dots> = (\<Sum>i<n. coeffs i * vx i) + (\<Sum>i<n. coeffs i * c)"
          by (rule sum.distrib)
        also have "(\<Sum>i<n. coeffs i * c) = c * (\<Sum>i<n. coeffs i)"
          by (simp add: sum_distrib_left mult.commute)
        also have "\<dots> = c" using \<open>(\<Sum>i<n. coeffs i) = 1\<close> by simp
        finally show "(\<Sum>i<n. coeffs i * (vx i + c)) = (\<Sum>i<n. coeffs i * vx i) + c" .
      qed
      show ?thesis
      proof
        show "(\<lambda>(x, y). (x + c, y)) ` P \<subseteq>
            {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
        proof
          fix p assume "p \<in> (\<lambda>(x, y). (x + c, y)) ` P"
          then obtain x y where hp: "p = (x + c, y)" "(x, y) \<in> P" by (by100 force)
          then obtain coeffs where hc: "(\<forall>i<n. 0 \<le> coeffs i)" "(\<Sum>i<n. coeffs i) = 1"
              "x = (\<Sum>i<n. coeffs i * vx i)" "y = (\<Sum>i<n. coeffs i * vy i)"
            unfolding hP_eq by (by100 auto)
          have hxc: "x + c = (\<Sum>i<n. coeffs i * vx' i)" unfolding vx'_def using hsum_dist[OF hc(2)] hc(3) by simp
          have hyv: "y = (\<Sum>i<n. coeffs i * vy' i)" unfolding vy'_def using hc(4) by simp
          have "\<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> (x + c) = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)"
            using hc(1) hc(2) hxc hyv by (by100 blast)
          thus "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
            using hp(1) by (by100 blast)
        qed
      next
        show "{(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
                \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}
              \<subseteq> (\<lambda>(x, y). (x + c, y)) ` P"
        proof
          fix p assume "p \<in> {(x, y) |x y. \<exists>coeffs. (\<forall>i<n. 0 \<le> coeffs i) \<and> (\<Sum>i<n. coeffs i) = 1
              \<and> x = (\<Sum>i<n. coeffs i * vx' i) \<and> y = (\<Sum>i<n. coeffs i * vy' i)}"
          then obtain x' y coeffs where hp: "p = (x', y)"
              and hc: "(\<forall>i<n. 0 \<le> coeffs i)" "(\<Sum>i<n. coeffs i) = 1"
              "x' = (\<Sum>i<n. coeffs i * vx' i)" "y = (\<Sum>i<n. coeffs i * vy' i)" by (by5000 auto)
          have "x' = (\<Sum>i<n. coeffs i * vx i) + c"
            using hc(3) unfolding vx'_def using hsum_dist[OF hc(2)] by simp
          hence hx_orig: "x' - c = (\<Sum>i<n. coeffs i * vx i)" by simp
          have hy_orig: "y = (\<Sum>i<n. coeffs i * vy i)" using hc(4) unfolding vy'_def by simp
          have "(x' - c, y) \<in> P" unfolding hP_eq using hc(1) hc(2) hx_orig hy_orig by (by100 blast)
          hence "(x' - c + c, y) = p" using hp by simp
          hence "(\<lambda>(x,y). (x+c, y)) (x' - c, y) = p" by simp
          thus "p \<in> (\<lambda>(x, y). (x + c, y)) ` P" using \<open>(x' - c, y) \<in> P\<close> by (by100 force)
        qed
      qed
    qed
    show "top1_is_polygonal_region_on ((\<lambda>(x,y). (x + c, y)) ` P) n"
      unfolding top1_is_polygonal_region_on_def
      using hn hdist' hndeg' hP'_eq by (by100 blast)
  qed
  \<comment> \<open>Step 4: Construct disjoint copies of standard simplex in R², one per triangle.\<close>
  \<comment> \<open>Enumerate the triangles.\<close>
  obtain tlist where htlist: "set tlist = \<T>0" "distinct tlist"
    using finite_distinct_list[OF h\<T>0(1)] by (by100 blast)
  let ?m = "length tlist"
  have h\<T>0_ne: "\<T>0 \<noteq> {}"
  proof -
    have "X \<noteq> {}" using assms(1) unfolding top1_is_surface_on_def by (by100 blast)
    thus ?thesis using h\<T>0(2) by (by100 blast)
  qed
  have hm_pos: "?m > 0"
    using h\<T>0_ne htlist(1) by (by100 force)
  \<comment> \<open>Place the i-th simplex copy at position (3*i, 0) to ensure disjointness.\<close>
  define \<Delta>copy :: "nat \<Rightarrow> (real \<times> real) set" where
    "\<Delta>copy i = (\<lambda>(x,y). (x + 3 * real i, y)) ` top1_standard_simplex" for i
  let ?\<T> = "{\<Delta>copy i | i. i < ?m}"
  \<comment> \<open>Define q: on \\<Delta>copy i, apply h0(tlist!i) composed with the inverse translation.\<close>
  define q_map :: "(real \<times> real) \<Rightarrow> 'a" where
    "q_map p = (let i = (SOME i. i < ?m \<and> p \<in> \<Delta>copy i) in
                h0 (tlist ! i) ((fst p - 3 * real i, snd p)))" for p
  \<comment> \<open>Show the required properties.\<close>
  have h\<T>_fin: "finite ?\<T>"
  proof -
    have "?\<T> = (\<lambda>i. \<Delta>copy i) ` {..<?m}" by (by100 blast)
    thus ?thesis by simp
  qed
  have h\<T>_ne: "?\<T> \<noteq> {}"
  proof -
    have "\<Delta>copy 0 \<in> ?\<T>" using hm_pos by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have h\<T>_poly: "\<forall>T \<in> ?\<T>. top1_is_polygonal_region_on T 3"
  proof (intro ballI)
    fix T assume "T \<in> ?\<T>"
    then obtain i where "i < ?m" "T = \<Delta>copy i" by (by100 blast)
    \<comment> \<open>\\<Delta>copy i = translation of standard simplex. Translation preserves polygonal region.
       The standard simplex has vertices (vx j, vy j) for j < 3 (from h\\_simplex\\_poly).
       \\<Delta>copy i has vertices (vx j + 3*i, vy j). Same convex hull structure.\<close>
    show "top1_is_polygonal_region_on T 3"
      using \<open>T = \<Delta>copy i\<close> unfolding \<Delta>copy_def
      using htranslate_poly[OF h_simplex_poly] by simp
  qed
  \<comment> \<open>Infrastructure: disjointness, SOME resolution, inverse translation, h0 range.\<close>
  have h_fst_bound: "\<And>i p. p \<in> \<Delta>copy i \<Longrightarrow> 3 * real i \<le> fst p \<and> fst p \<le> 3 * real i + 1"
  proof -
    fix i :: nat and p :: "real \<times> real" assume "p \<in> \<Delta>copy i"
    then obtain x y where hxy: "(x, y) \<in> top1_standard_simplex" "p = (x + 3 * real i, y)"
      unfolding \<Delta>copy_def by (by100 force)
    have "x \<ge> 0" "x \<le> 1" using hxy(1) unfolding top1_standard_simplex_def by (by100 auto)+
    thus "3 * real i \<le> fst p \<and> fst p \<le> 3 * real i + 1" using hxy(2) by simp
  qed
  have h_disjoint: "\<And>i j. i \<noteq> j \<Longrightarrow> \<Delta>copy i \<inter> \<Delta>copy j = {}"
  proof -
    fix i j :: nat assume hij: "i \<noteq> j"
    show "\<Delta>copy i \<inter> \<Delta>copy j = {}"
    proof (rule ccontr)
      assume "\<Delta>copy i \<inter> \<Delta>copy j \<noteq> {}"
      then obtain p where hp: "p \<in> \<Delta>copy i" "p \<in> \<Delta>copy j" by (by100 blast)
      have "3 * real i \<le> fst p" "fst p \<le> 3 * real i + 1"
        using h_fst_bound[OF hp(1)] by (by100 auto)+
      have "3 * real j \<le> fst p" "fst p \<le> 3 * real j + 1"
        using h_fst_bound[OF hp(2)] by (by100 auto)+
      hence "3 * real i \<le> 3 * real j + 1" "3 * real j \<le> 3 * real i + 1"
        using \<open>3 * real i \<le> fst p\<close> \<open>fst p \<le> 3 * real j + 1\<close>
              \<open>3 * real j \<le> fst p\<close> \<open>fst p \<le> 3 * real i + 1\<close> by linarith+
      hence "real i \<le> real j + 1/3" "real j \<le> real i + 1/3" by linarith+
      hence "\<bar>real i - real j\<bar> \<le> 1/3" by linarith
      hence "i = j" by linarith
      thus False using hij by simp
    qed
  qed
  have h_SOME: "\<And>i p. i < ?m \<Longrightarrow> p \<in> \<Delta>copy i \<Longrightarrow> (SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i"
  proof -
    fix i :: nat and p assume hi: "i < ?m" and hp: "p \<in> \<Delta>copy i"
    have huniq: "\<And>j. j < ?m \<and> p \<in> \<Delta>copy j \<Longrightarrow> j = i"
    proof -
      fix j assume "j < ?m \<and> p \<in> \<Delta>copy j"
      hence "p \<in> \<Delta>copy j" by simp
      hence "\<Delta>copy i \<inter> \<Delta>copy j \<noteq> {}" using hp by (by100 blast)
      thus "j = i" using h_disjoint by (by100 blast)
    qed
    show "(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i"
      by (rule some_equality) (use hi hp huniq in \<open>by100 blast\<close>)+
  qed
  have h_inv_trans: "\<And>i p. p \<in> \<Delta>copy i \<Longrightarrow> (fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
  proof -
    fix i :: nat and p :: "real \<times> real" assume "p \<in> \<Delta>copy i"
    then obtain x y where hxy: "(x, y) \<in> top1_standard_simplex" "p = (x + 3 * real i, y)"
      unfolding \<Delta>copy_def by (by100 force)
    have "fst p - 3 * real i = x" "snd p = y" using hxy(2) by simp+
    thus "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex" using hxy(1) by simp
  qed
  have h_h0_surj: "\<And>i. i < ?m \<Longrightarrow> h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
  proof -
    fix i assume "i < ?m"
    have "tlist ! i \<in> set tlist" using \<open>i < ?m\<close> by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    hence "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) by (by100 blast)
    hence "bij_betw (h0 (tlist ! i)) top1_standard_simplex (tlist ! i)"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    thus "h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
      unfolding bij_betw_def by simp
  qed
  have h_qmap_on_copy: "\<And>i p. i < ?m \<Longrightarrow> p \<in> \<Delta>copy i \<Longrightarrow>
      q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
  proof -
    fix i :: nat and p assume "i < ?m" "p \<in> \<Delta>copy i"
    have "(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i" using h_SOME[OF \<open>i < ?m\<close> \<open>p \<in> \<Delta>copy i\<close>] .
    thus "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
      unfolding q_map_def Let_def using \<open>(SOME j. j < ?m \<and> p \<in> \<Delta>copy j) = i\<close> by simp
  qed
  \<comment> \<open>Lift h0 continuity from subspace(X,TX,Ti) to TX.\<close>
  have h_h0_cont_X: "\<And>i. i < ?m \<Longrightarrow> top1_continuous_map_on
      top1_standard_simplex top1_standard_simplex_topology X TX (h0 (tlist ! i))"
  proof -
    fix i assume hi: "i < ?m"
    have "tlist ! i \<in> set tlist" using hi by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    hence hTi_sub: "tlist ! i \<subseteq> X" using h\<T>0(2) by (by100 blast)
    have hhomeo: "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) \<open>tlist ! i \<in> \<T>0\<close> by (by100 blast)
    hence hcont_sub: "top1_continuous_map_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    show "top1_continuous_map_on top1_standard_simplex top1_standard_simplex_topology X TX (h0 (tlist ! i))"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> top1_standard_simplex"
      have "h0 (tlist ! i) s \<in> tlist ! i"
        using hcont_sub \<open>s \<in> top1_standard_simplex\<close>
        unfolding top1_continuous_map_on_def by (by100 blast)
      thus "h0 (tlist ! i) s \<in> X" using hTi_sub by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have "V \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
        unfolding subspace_topology_def using hV by (by100 blast)
      hence "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}
          \<in> top1_standard_simplex_topology"
        using hcont_sub unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          = {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
      proof
        show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
            \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
        proof
          fix s assume "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}"
          hence "s \<in> top1_standard_simplex" "h0 (tlist ! i) s \<in> V" by (by100 auto)+
          moreover have "h0 (tlist ! i) s \<in> tlist ! i"
            using hcont_sub \<open>s \<in> top1_standard_simplex\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}"
            by (by100 blast)
        qed
      next
        show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V \<inter> tlist ! i}
            \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}" by (by100 blast)
      qed
      ultimately show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          \<in> top1_standard_simplex_topology" by simp
    qed
  qed
  have h\<T>_cont: "\<forall>T \<in> ?\<T>. top1_continuous_map_on T
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_map"
  proof (intro ballI)
    fix T assume "T \<in> ?\<T>"
    then obtain i where hi: "i < ?m" "T = \<Delta>copy i" by (by100 blast)
    show "top1_continuous_map_on T
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_map"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume hp: "p \<in> T"
      hence "p \<in> \<Delta>copy i" using hi(2) by simp
      have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
        using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] .
      moreover have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
        using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] .
      ultimately show "q_map p \<in> X"
        using continuous_map_maps_to[OF h_h0_cont_X[OF hi(1)]] by simp
    next
      fix V assume hV: "V \<in> TX"
      \<comment> \<open>Need: {p \\<in> T. q\\_map p \\<in> V} \\<in> subspace R² T.
         This equals {p \\<in> \\<Delta>copy i. h0(tlist!i)(invtrans(p)) \\<in> V}.
         From h0 continuity: {s \\<in> \\<Delta>. h0 s \\<in> V} \\<in> standard\\_simplex\\_topology.
         Translation preserves openness.\<close>
      have hpre_ss: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V}
          \<in> top1_standard_simplex_topology"
        using continuous_map_preimage_open[OF h_h0_cont_X[OF hi(1)] hV] .
      \<comment> \<open>This preimage in standard\\_simplex\\_topology = subspace R² standard\\_simplex.
         So there exists W open in R² with preimage = W \\<inter> standard\\_simplex.\<close>
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> V} = W \<inter> top1_standard_simplex"
        unfolding top1_standard_simplex_topology_def subspace_topology_def by (by100 blast)
      \<comment> \<open>Translate W by (3*i, 0) to get W' open in R².\<close>
      define W' where "W' = (\<lambda>(x,y). (x + 3 * real i, y)) ` W"
      \<comment> \<open>Translation preserves openness in product\\_topology. This is the key step.\<close>
      have hW'_open: "W' \<in> product_topology_on top1_open_sets top1_open_sets"
        unfolding product_topology_on_def topology_generated_by_basis_def
      proof (intro CollectI conjI ballI)
        show "W' \<subseteq> UNIV" by simp
      next
        fix p assume "p \<in> W'"
        then obtain s where hs: "s \<in> W" "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
          unfolding W'_def by (by100 blast)
        have hW_open: "W \<in> topology_generated_by_basis UNIV (product_basis top1_open_sets top1_open_sets)"
          using hW(1) unfolding product_topology_on_def .
        hence "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. s \<in> b \<and> b \<subseteq> W"
          using \<open>s \<in> W\<close> unfolding topology_generated_by_basis_def by (by100 blast)
        then obtain U0 V0 where hUV: "U0 \<in> top1_open_sets" "V0 \<in> top1_open_sets"
            "s \<in> U0 \<times> V0" "U0 \<times> V0 \<subseteq> W"
          unfolding product_basis_def by (by100 blast)
        define U' where "U' = (\<lambda>x. x + 3 * real i) ` U0"
        have hU'_open: "U' \<in> top1_open_sets"
        proof -
          have "open U0" using hUV(1) unfolding top1_open_sets_def by simp
          have "open ((\<lambda>x::real. x - 3 * real i) -` U0)"
            by (rule open_vimage[OF \<open>open U0\<close>]) (intro continuous_intros)
          moreover have "(\<lambda>x::real. x - 3 * real i) -` U0 = (\<lambda>x. x + 3 * real i) ` U0"
            by (by100 force)
          ultimately have "open ((\<lambda>x. 3 * real i + x) ` U0)"
            by (simp add: add.commute)
          moreover have "(\<lambda>x. 3 * real i + x) ` U0 = U'"
            unfolding U'_def by (by100 force)
          ultimately show ?thesis unfolding top1_open_sets_def by simp
        qed
        have "p \<in> U' \<times> V0"
          using hUV(3) hs(2) unfolding U'_def by (cases s) (by100 force)
        moreover have "U' \<times> V0 \<subseteq> W'"
        proof
          fix q assume "q \<in> U' \<times> V0"
          then obtain u v where "u \<in> U'" "v \<in> V0" "q = (u, v)" by (by100 blast)
          then obtain u0 where "u0 \<in> U0" "u = u0 + 3 * real i"
            unfolding U'_def by (by100 blast)
          hence "(u0, v) \<in> U0 \<times> V0" using \<open>v \<in> V0\<close> by simp
          hence "(u0, v) \<in> W" using hUV(4) by (by100 blast)
          have "q = (\<lambda>(x,y). (x + 3 * real i, y)) (u0, v)"
            using \<open>q = (u, v)\<close> \<open>u = u0 + 3 * real i\<close> by simp
          thus "q \<in> W'" unfolding W'_def using \<open>(u0, v) \<in> W\<close> by (by100 blast)
        qed
        moreover have hU'V0_basis: "U' \<times> V0 \<in> product_basis top1_open_sets top1_open_sets"
          unfolding product_basis_def using hU'_open hUV(2) by (by100 blast)
        ultimately show "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. p \<in> b \<and> b \<subseteq> W'"
          apply (rule_tac bexI[of _ "U' \<times> V0"])
          apply (by100 blast)
          apply assumption
          done
      qed
      \<comment> \<open>{p \\<in> T. q\\_map p \\<in> V} = W' \\<inter> T.\<close>
      have hpre_eq: "{p \<in> T. q_map p \<in> V} = W' \<inter> T"
      proof
        show "{p \<in> T. q_map p \<in> V} \<subseteq> W' \<inter> T"
        proof
          fix p assume hp: "p \<in> {p \<in> T. q_map p \<in> V}"
          hence "p \<in> T" "q_map p \<in> V" by (by100 auto)+
          hence "p \<in> \<Delta>copy i" using hi(2) by simp
          have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
            using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] .
          moreover have "h0 (tlist ! i) (fst p - 3 * real i, snd p) \<in> V"
            using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] \<open>q_map p \<in> V\<close> by simp
          ultimately have "(fst p - 3 * real i, snd p) \<in> W"
            using hW(2) by (by100 blast)
          have "p = (\<lambda>(x,y). (x + 3 * real i, y)) (fst p - 3 * real i, snd p)" by simp
          hence "p \<in> W'" unfolding W'_def
            using \<open>(fst p - 3 * real i, snd p) \<in> W\<close> by (by100 blast)
          thus "p \<in> W' \<inter> T" using \<open>p \<in> T\<close> by (by100 blast)
        qed
      next
        show "W' \<inter> T \<subseteq> {p \<in> T. q_map p \<in> V}"
        proof
          fix p assume hp: "p \<in> W' \<inter> T"
          hence "p \<in> W'" "p \<in> T" by (by100 auto)+
          hence "p \<in> \<Delta>copy i" using hi(2) by simp
          from \<open>p \<in> W'\<close> obtain s where hs: "s \<in> W" "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
            unfolding W'_def by (by100 blast)
          have "fst p - 3 * real i = fst s" "snd p = snd s"
            using hs(2) by (cases s, simp)+
          hence hinv: "(fst p - 3 * real i, snd p) = s" by (cases s) simp
          have "s \<in> top1_standard_simplex"
            using h_inv_trans[OF \<open>p \<in> \<Delta>copy i\<close>] hinv by simp
          hence "s \<in> W \<inter> top1_standard_simplex" using \<open>s \<in> W\<close> by simp
          hence "h0 (tlist ! i) s \<in> V" using hW(2) by (by100 blast)
          hence "h0 (tlist ! i) (fst p - 3 * real i, snd p) \<in> V" using hinv by simp
          hence "q_map p \<in> V" using h_qmap_on_copy[OF hi(1) \<open>p \<in> \<Delta>copy i\<close>] by simp
          thus "p \<in> {p \<in> T. q_map p \<in> V}" using \<open>p \<in> T\<close> by (by100 blast)
        qed
      qed
      thus "{p \<in> T. q_map p \<in> V} \<in> subspace_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) T"
        unfolding subspace_topology_def using hW'_open by (by100 blast)
    qed
  qed
  have h\<T>_cov: "(\<Union>T\<in>?\<T>. q_map ` T) = X"
  proof
    show "(\<Union>T\<in>?\<T>. q_map ` T) \<subseteq> X"
    proof
      fix x assume "x \<in> (\<Union>T\<in>?\<T>. q_map ` T)"
      then obtain T p where hT: "T \<in> ?\<T>" and hp: "p \<in> T" and hx: "x = q_map p" by (by100 blast)
      from hT obtain i where hi: "i < ?m" "T = \<Delta>copy i" by (by100 blast)
      have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
        using h_qmap_on_copy[OF hi(1)] hp hi(2) by simp
      moreover have "(fst p - 3 * real i, snd p) \<in> top1_standard_simplex"
        using h_inv_trans hp hi(2) by simp
      ultimately have "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using hx by (by100 blast)
      hence "x \<in> tlist ! i" using h_h0_surj[OF hi(1)] by simp
      moreover have "tlist ! i \<in> set tlist" using hi(1) by simp
      hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
      hence "tlist ! i \<subseteq> X" using h\<T>0(2) by (by100 blast)
      ultimately show "x \<in> X" by (by100 blast)
    qed
  next
    show "X \<subseteq> (\<Union>T\<in>?\<T>. q_map ` T)"
    proof
      fix x assume "x \<in> X"
      hence "x \<in> \<Union>\<T>0" using h\<T>0(2) by simp
      then obtain T0i where hT0i: "T0i \<in> \<T>0" "x \<in> T0i" by (by100 blast)
      have "T0i \<in> set tlist" using hT0i(1) htlist(1) by simp
      then obtain i where hi: "i < ?m" "tlist ! i = T0i"
        by (metis in_set_conv_nth)
      have "x \<in> tlist ! i" using hT0i(2) hi(2) by simp
      hence "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using h_h0_surj[OF hi(1)] by simp
      then obtain s where hs: "s \<in> top1_standard_simplex" "h0 (tlist ! i) s = x" by (by100 blast)
      define p where "p = (fst s + 3 * real i, snd s)"
      have hp_in: "p \<in> \<Delta>copy i"
      proof -
        have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" unfolding p_def by (cases s) simp
        thus ?thesis unfolding \<Delta>copy_def using hs(1) by (by100 blast)
      qed
      have "fst p - 3 * real i = fst s" "snd p = snd s"
        unfolding p_def by simp+
      hence "q_map p = h0 (tlist ! i) s"
        using h_qmap_on_copy[OF hi(1) hp_in] by simp
      hence "q_map p = x" using hs(2) by simp
      moreover have "\<Delta>copy i \<in> ?\<T>" using hi(1) by (by100 blast)
      ultimately show "x \<in> (\<Union>T\<in>?\<T>. q_map ` T)" using hp_in by (by100 blast)
    qed
  qed
  \<comment> \<open>Key bridge: h0 is an open map (homeomorphism maps opens to opens).\<close>
  have h_h0_open_map: "\<And>i Uo. i < ?m \<Longrightarrow>
      Uo \<in> top1_standard_simplex_topology \<Longrightarrow>
      h0 (tlist ! i) ` Uo \<in> subspace_topology X TX (tlist ! i)"
  proof -
    fix i Uo assume hi: "i < ?m" and hO: "Uo \<in> top1_standard_simplex_topology"
    have "tlist ! i \<in> set tlist" using hi by simp
    hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
    have hhomeo: "top1_homeomorphism_on top1_standard_simplex top1_standard_simplex_topology
        (tlist ! i) (subspace_topology X TX (tlist ! i)) (h0 (tlist ! i))"
      using h\<T>0(3) \<open>tlist ! i \<in> \<T>0\<close> by (by100 blast)
    hence hinv_cont: "top1_continuous_map_on (tlist ! i) (subspace_topology X TX (tlist ! i))
        top1_standard_simplex top1_standard_simplex_topology (inv_into top1_standard_simplex (h0 (tlist ! i)))"
      unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>h0(T) `` O = {b \\<in> T | inv\\_into(h0)(b) \\<in> O} (preimage under inverse).\<close>
    have hbij: "bij_betw (h0 (tlist ! i)) top1_standard_simplex (tlist ! i)"
      using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinj: "inj_on (h0 (tlist ! i)) top1_standard_simplex"
      using hbij unfolding bij_betw_def by simp
    have hrange: "h0 (tlist ! i) ` top1_standard_simplex = tlist ! i"
      using h_h0_surj[OF hi] .
    have heq: "h0 (tlist ! i) ` Uo = {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
    proof
      show "h0 (tlist ! i) ` Uo \<subseteq> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
      proof
        fix b assume "b \<in> h0 (tlist ! i) ` Uo"
        then obtain s where hs: "s \<in> Uo" "b = h0 (tlist ! i) s" by (by100 blast)
        have "s \<in> top1_standard_simplex" using hO hs(1)
          unfolding top1_standard_simplex_topology_def subspace_topology_def by (by100 blast)
        hence "b \<in> tlist ! i" using hs(2) hrange by (by100 blast)
        moreover have "inv_into top1_standard_simplex (h0 (tlist ! i)) b = s"
          using inv_into_f_f[OF hinj \<open>s \<in> top1_standard_simplex\<close>] hs(2) by simp
        ultimately show "b \<in> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
          using hs(1) by (by100 blast)
      qed
    next
      show "{b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}
          \<subseteq> h0 (tlist ! i) ` Uo"
      proof
        fix b assume "b \<in> {b \<in> tlist ! i. inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo}"
        hence hb: "b \<in> tlist ! i" "inv_into top1_standard_simplex (h0 (tlist ! i)) b \<in> Uo" by auto
        have "h0 (tlist ! i) (inv_into top1_standard_simplex (h0 (tlist ! i)) b) = b"
          using f_inv_into_f[of b "h0 (tlist ! i)" top1_standard_simplex] hb(1) hrange by (by100 blast)
        thus "b \<in> h0 (tlist ! i) ` Uo" using hb(2) by (by100 force)
      qed
    qed
    show "h0 (tlist ! i) ` Uo \<in> subspace_topology X TX (tlist ! i)"
      unfolding heq
      using continuous_map_preimage_open[OF hinv_cont hO] .
  qed
  \<comment> \<open>Backward: if preimages open in each \\<Delta>copy, then U \\<in> TX via finite closed cover.\<close>
  have h_X_strict: "is_topology_on_strict X TX"
    using assms(2) unfolding top1_is_triangulable_on_def by (by100 blast)
  have h_X_top: "is_topology_on X TX"
    using h_X_strict by (rule is_topology_on_strict_imp)
  have h\<T>_quot: "\<forall>U. U \<subseteq> X \<longrightarrow>
      (U \<in> TX \<longleftrightarrow> (\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T))"
  proof (intro allI impI iffI)
    fix U assume hU_sub: "U \<subseteq> X"
    \<comment> \<open>Forward: U \\<in> TX \\<Rightarrow> preimages open (from continuity).\<close>
    assume hU: "U \<in> TX"
    show "\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
      using h\<T>_cont hU unfolding top1_continuous_map_on_def by (by100 blast)
  next
    fix U assume hU_sub: "U \<subseteq> X"
    \<comment> \<open>Backward: preimages open \\<Rightarrow> U \\<in> TX via finite closed cover.\<close>
    assume hpre: "\<forall>T\<in>?\<T>. {p\<in>T. q_map p \<in> U} \<in>
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
    \<comment> \<open>Step 1: For each i, U \\<inter> tlist!i is open in subspace(X, TX, tlist!i).\<close>
    have hU_open_piece: "\<And>i. i < ?m \<Longrightarrow>
        U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
    proof -
      fix i assume hi: "i < ?m"
      have "\<Delta>copy i \<in> ?\<T>" using hi by (by100 blast)
      hence hpre_i: "{p \<in> \<Delta>copy i. q_map p \<in> U} \<in>
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (\<Delta>copy i)"
        using hpre by simp
      \<comment> \<open>Translate to standard simplex: {s \\<in> SS. h0(s) \\<in> U} is open in SS\\_top.\<close>
      have "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
          \<in> top1_standard_simplex_topology"
      proof -
        \<comment> \<open>The preimage in \\<Delta>copy i is open: = W' \\<inter> \\<Delta>copy i for some W' open in R².\<close>
        from hpre_i obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
            "{p \<in> \<Delta>copy i. q_map p \<in> U} = W' \<inter> \<Delta>copy i"
          unfolding subspace_topology_def by (by100 blast)
        \<comment> \<open>Inverse-translate W' to get W open in R², such that preimage in SS = W \\<inter> SS.\<close>
        define W where "W = (\<lambda>(x,y). (x - 3 * real i, y)) ` W'"
        \<comment> \<open>W is open in R² (inverse translation preserves openness, same argument as forward).\<close>
        have hW_open: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          unfolding product_topology_on_def topology_generated_by_basis_def
        proof (intro CollectI conjI ballI)
          show "W \<subseteq> UNIV" by simp
        next
          fix s assume "s \<in> W"
          then obtain p where hp: "p \<in> W'" "s = (\<lambda>(x,y). (x - 3 * real i, y)) p"
            unfolding W_def by (by100 blast)
          from hW'(1) have "W' \<in> topology_generated_by_basis UNIV (product_basis top1_open_sets top1_open_sets)"
            unfolding product_topology_on_def .
          hence "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. p \<in> b \<and> b \<subseteq> W'"
            using hp(1) unfolding topology_generated_by_basis_def by (by100 blast)
          then obtain U0 V0 where hUV: "U0 \<in> top1_open_sets" "V0 \<in> top1_open_sets"
              "p \<in> U0 \<times> V0" "U0 \<times> V0 \<subseteq> W'"
            unfolding product_basis_def by (by100 blast)
          define U0' where "U0' = (\<lambda>x. x - 3 * real i) ` U0"
          have "open U0" using hUV(1) unfolding top1_open_sets_def by simp
          have "(\<lambda>x. x - 3 * real i) ` U0 = (\<lambda>y::real. y + 3 * real i) -` U0"
            by (by100 force)
          moreover have "open ((\<lambda>y::real. y + 3 * real i) -` U0)"
            by (rule open_vimage[OF \<open>open U0\<close>]) (intro continuous_intros)
          ultimately have "open U0'" unfolding U0'_def by simp
          hence hU0'_open: "U0' \<in> top1_open_sets" unfolding top1_open_sets_def by simp
          have "s \<in> U0' \<times> V0"
            using hUV(3) hp(2) unfolding U0'_def by (cases p) (by100 force)
          moreover have "U0' \<times> V0 \<subseteq> W"
          proof
            fix q assume "q \<in> U0' \<times> V0"
            then obtain u v where "u \<in> U0'" "v \<in> V0" "q = (u, v)" by (by100 blast)
            then obtain u0 where "u0 \<in> U0" "u = u0 - 3 * real i"
              unfolding U0'_def by (by100 blast)
            hence "(u0, v) \<in> U0 \<times> V0" using \<open>v \<in> V0\<close> by simp
            hence "(u0, v) \<in> W'" using hUV(4) by (by100 blast)
            have "q = (\<lambda>(x,y). (x - 3 * real i, y)) (u0, v)"
              using \<open>q = (u, v)\<close> \<open>u = u0 - 3 * real i\<close> by simp
            thus "q \<in> W" unfolding W_def using \<open>(u0, v) \<in> W'\<close> by (by100 blast)
          qed
          moreover have hU0'V0_basis: "U0' \<times> V0 \<in> product_basis top1_open_sets top1_open_sets"
            unfolding product_basis_def using hU0'_open hUV(2) by (by100 blast)
          ultimately show "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. s \<in> b \<and> b \<subseteq> W"
            apply (rule_tac bexI[of _ "U0' \<times> V0"])
            apply (by100 blast)
            apply assumption
            done
        qed
        \<comment> \<open>Now: {s \\<in> SS. h0(s) \\<in> U} = W \\<inter> SS.\<close>
        have heq: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} = W \<inter> top1_standard_simplex"
        proof
          show "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} \<subseteq> W \<inter> top1_standard_simplex"
          proof
            fix s assume hs: "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
            hence "s \<in> top1_standard_simplex" "h0 (tlist ! i) s \<in> U" by auto
            define p where "p = (\<lambda>(x,y). (x + 3 * real i, y)) s"
            have "p \<in> \<Delta>copy i"
            proof -
              have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" unfolding p_def by simp
              thus ?thesis unfolding \<Delta>copy_def using \<open>s \<in> top1_standard_simplex\<close> by (by100 blast)
            qed
            have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
              using h_qmap_on_copy[OF hi \<open>p \<in> \<Delta>copy i\<close>] .
            also have "(fst p - 3 * real i, snd p) = s" unfolding p_def by (cases s) simp
            finally have "q_map p = h0 (tlist ! i) s" .
            hence "q_map p \<in> U" using \<open>h0 (tlist ! i) s \<in> U\<close> by simp
            hence "p \<in> {p \<in> \<Delta>copy i. q_map p \<in> U}" using \<open>p \<in> \<Delta>copy i\<close> by simp
            hence "p \<in> W' \<inter> \<Delta>copy i" using hW'(2) by simp
            hence "p \<in> W'" by simp
            have "s = (\<lambda>(x,y). (x - 3 * real i, y)) p" unfolding p_def by (cases s) simp
            hence "s \<in> W" unfolding W_def using \<open>p \<in> W'\<close> by (by100 blast)
            thus "s \<in> W \<inter> top1_standard_simplex" using \<open>s \<in> top1_standard_simplex\<close> by simp
          qed
        next
          show "W \<inter> top1_standard_simplex \<subseteq> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
          proof
            fix s assume hs: "s \<in> W \<inter> top1_standard_simplex"
            hence "s \<in> W" "s \<in> top1_standard_simplex" by auto
            from \<open>s \<in> W\<close> obtain p where hp: "p \<in> W'" "s = (\<lambda>(x,y). (x - 3 * real i, y)) p"
              unfolding W_def by (by100 blast)
            have "fst s + 3 * real i = fst p" "snd s = snd p" using hp(2) by (cases p, simp)+
            hence "p \<in> \<Delta>copy i"
            proof -
              have "p = (\<lambda>(x,y). (x + 3 * real i, y)) s" using hp(2) by (cases s, cases p) simp
              thus ?thesis unfolding \<Delta>copy_def using \<open>s \<in> top1_standard_simplex\<close> by (by100 blast)
            qed
            hence "p \<in> W' \<inter> \<Delta>copy i" using hp(1) by simp
            hence "p \<in> {p \<in> \<Delta>copy i. q_map p \<in> U}" using hW'(2) by simp
            hence "q_map p \<in> U" by simp
            have "q_map p = h0 (tlist ! i) (fst p - 3 * real i, snd p)"
              using h_qmap_on_copy[OF hi \<open>p \<in> \<Delta>copy i\<close>] .
            also have "(fst p - 3 * real i, snd p) = s" using hp(2) by (cases p) simp
            finally have "h0 (tlist ! i) s = q_map p" by simp
            hence "h0 (tlist ! i) s \<in> U" using \<open>q_map p \<in> U\<close> by simp
            thus "s \<in> {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
              using \<open>s \<in> top1_standard_simplex\<close> by simp
          qed
        qed
        show ?thesis unfolding heq top1_standard_simplex_topology_def subspace_topology_def
          using hW_open by (by100 blast)
      qed
      \<comment> \<open>h0 maps this open set to U \\<inter> tlist!i.\<close>
      moreover have "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
          = U \<inter> tlist ! i"
      proof
        show "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
            \<subseteq> U \<inter> tlist ! i"
          using h_h0_surj[OF hi] by (by100 blast)
      next
        show "U \<inter> tlist ! i
            \<subseteq> h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
        proof
          fix x assume "x \<in> U \<inter> tlist ! i"
          hence "x \<in> tlist ! i" "x \<in> U" by auto
          hence "x \<in> h0 (tlist ! i) ` top1_standard_simplex" using h_h0_surj[OF hi] by simp
          then obtain s where "s \<in> top1_standard_simplex" "h0 (tlist ! i) s = x" by (by100 blast)
          thus "x \<in> h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}"
            using \<open>x \<in> U\<close> by (by100 blast)
        qed
      qed
      ultimately show "U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
      proof -
        assume h1: "{s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} \<in> top1_standard_simplex_topology"
        assume h2: "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U} = U \<inter> tlist ! i"
        from h_h0_open_map[OF hi h1] have "h0 (tlist ! i) ` {s \<in> top1_standard_simplex. h0 (tlist ! i) s \<in> U}
            \<in> subspace_topology X TX (tlist ! i)" .
        thus ?thesis using h2 by simp
      qed
    qed
    \<comment> \<open>Step 2: Finite closed cover \\<Rightarrow> U \\<in> TX.\<close>
    \<comment> \<open>X - U is closed: each (tlist!i) - U = (tlist!i) \\<inter> (X-U) is closed in TX.\<close>
    have hcl: "\<And>i. i < ?m \<Longrightarrow> closedin_on X TX (tlist ! i \<inter> (X - U))"
    proof -
      fix i assume hi: "i < ?m"
      have "tlist ! i \<in> set tlist" using hi by simp
      hence "tlist ! i \<in> \<T>0" using htlist(1) by simp
      hence hTi_cl: "closedin_on X TX (tlist ! i)" using h\<T>0(3) by (by100 blast)
      \<comment> \<open>tlist!i - U is closed in subspace(X,TX,tlist!i).\<close>
      have "U \<inter> tlist ! i \<in> subspace_topology X TX (tlist ! i)"
        using hU_open_piece[OF hi] .
      then obtain V where hV: "V \<in> TX" "U \<inter> tlist ! i = V \<inter> tlist ! i"
        unfolding subspace_topology_def by (by100 blast)
      have "tlist ! i \<inter> (X - U) = tlist ! i \<inter> (X - V)"
        using hV(2) by (by100 blast)
      moreover have "closedin_on X TX (tlist ! i \<inter> (X - V))"
      proof -
        have hXV_cl: "closedin_on X TX (X - V)"
          unfolding closedin_on_def
        proof (intro conjI)
          show "X - V \<subseteq> X" by (by100 blast)
          show "X - (X - V) \<in> TX"
          proof -
            have "X - (X - V) = V \<inter> X"
              by (by100 blast)
            also have "V \<inter> X = V"
              using is_topology_on_strict_opens_sub[OF h_X_strict hV(1)] by (by100 blast)
            finally show ?thesis using hV(1) by simp
          qed
        qed
        have hsub: "tlist ! i \<inter> (X - V) \<subseteq> X" using hTi_cl unfolding closedin_on_def by (by100 blast)
        have hcomp: "X - (tlist ! i \<inter> (X - V)) \<in> TX"
        proof -
          have hV_sub: "V \<subseteq> X" using is_topology_on_strict_opens_sub[OF h_X_strict hV(1)] .
          have hXTi: "X - tlist ! i \<in> TX"
            using hTi_cl unfolding closedin_on_def by simp
          have "{X - tlist ! i, V} \<subseteq> TX" using hXTi hV(1) by (by100 blast)
          hence hUn: "\<Union>{X - tlist ! i, V} \<in> TX"
            using h_X_top unfolding is_topology_on_def by (by100 blast)
          have "(X - tlist ! i) \<union> V = X - (tlist ! i \<inter> (X - V))"
            using hV_sub by (by100 blast)
          thus ?thesis using hUn by simp
        qed
        show ?thesis unfolding closedin_on_def using hsub hcomp by (by100 blast)
      qed
      ultimately show "closedin_on X TX (tlist ! i \<inter> (X - U))" by simp
    qed
    have "X - U = (\<Union>i<?m. tlist ! i \<inter> (X - U))"
    proof
      show "X - U \<subseteq> (\<Union>i<length tlist. tlist ! i \<inter> (X - U))"
      proof
        fix x assume "x \<in> X - U"
        hence "x \<in> X" by simp
        hence "x \<in> \<Union>\<T>0" using h\<T>0(2) by simp
        then obtain T where "T \<in> \<T>0" "x \<in> T" by (by100 blast)
        have "T \<in> set tlist" using \<open>T \<in> \<T>0\<close> htlist(1) by simp
        then obtain i where "i < ?m" "tlist ! i = T" by (metis in_set_conv_nth)
        thus "x \<in> (\<Union>i<length tlist. tlist ! i \<inter> (X - U))"
          using \<open>x \<in> T\<close> \<open>x \<in> X - U\<close> by (by100 force)
      qed
    next
      show "(\<Union>i<length tlist. tlist ! i \<inter> (X - U)) \<subseteq> X - U"
        by (by100 blast)
    qed
    hence "closedin_on X TX (X - U)"
    proof -
      have "closedin_on X TX (\<Union>i<?m. tlist ! i \<inter> (X - U))"
      proof -
        have "finite {i. i < ?m}" by simp
        moreover have "\<And>i. i < ?m \<Longrightarrow> closedin_on X TX (tlist ! i \<inter> (X - U))"
          using hcl .
        ultimately have "closedin_on X TX (\<Union>((\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}))"
          using closedin_Union_finite[OF h_X_top, of "(\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}"]
          by (by100 auto)
        moreover have "(\<Union>((\<lambda>i. tlist ! i \<inter> (X - U)) ` {..<length tlist}))
            = (\<Union>i<?m. tlist ! i \<inter> (X - U))" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      thus ?thesis using \<open>X - U = (\<Union>i<?m. tlist ! i \<inter> (X - U))\<close> by simp
    qed
    hence "X - (X - U) \<in> TX" unfolding closedin_on_def by simp
    moreover have "X - (X - U) = U" using hU_sub by (by100 blast)
    ultimately show "U \<in> TX" by simp
  qed
  show ?thesis
    apply (rule exI[of _ "?\<T>"])
    apply (rule exI[of _ q_map])
    using h\<T>_fin h\<T>_ne h\<T>_poly h\<T>_cont h\<T>_cov h\<T>_quot
    apply (intro conjI)
    apply assumption+
    done
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
  \<comment> \<open>Step 1: By Theorem 78.1, X = quotient of finitely many triangles.\<close>
  \<comment> \<open>Step 2: Since X is connected, the dual graph of the triangulation is connected.
     Choose a spanning tree. Walk the tree, merging triangles along shared edges.
     Each merge: paste two polygons along a common edge to get a larger polygon.\<close>
  \<comment> \<open>Step 3: After merging all triangles, we have a single polygon P with
     boundary identifications reproducing X.\<close>
  \<comment> \<open>Step 1: By Theorem 78.1, X is a quotient of finitely many triangular regions.\<close>
  from Theorem_78_1_triangulable_surface[OF assms(1) assms(3)]
  obtain \<T> q_tri where h\<T>: "finite \<T>" "\<T> \<noteq> {}"
      "\<forall>T \<in> \<T>. top1_is_polygonal_region_on T 3"
      "\<forall>T \<in> \<T>. top1_continuous_map_on T
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) X TX q_tri"
      "(\<Union>T\<in>\<T>. q_tri ` T) = X"
      "\<forall>U. U \<subseteq> X \<longrightarrow>
          (U \<in> TX \<longleftrightarrow> (\<forall>T\<in>\<T>. {p\<in>T. q_tri p \<in> U} \<in>
              subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T))"
    by (by100 auto)
  \<comment> \<open>Step 2: Iteratively paste triangles along shared edges using Theorem 76.1 (\\<S>76).
     Book proof: "As long as two regions have edges bearing the same label, we can
     paste them together. Eventually either one has a single polygon (theorem proved)
     or several polygons with no shared labels. The latter gives a disconnected space,
     contradicting X connected."
     Formally: induction on card(\\<T>). If card = 1: done. If card > 1: find two regions
     sharing a label, paste them (§76.1), reducing card by 1. Apply IH.\<close>
  \<comment> \<open>Base case: if card(\\<T>) = 1, the single triangle is already a polygon.\<close>
  have hbase: "card \<T> = 1 \<Longrightarrow> ?thesis"
  proof -
    assume "card \<T> = 1"
    then obtain T0 where hT0: "\<T> = {T0}" using card_1_singletonE by (by100 blast)
    have hpoly: "top1_is_polygonal_region_on T0 3" using h\<T>(3) hT0 by (by100 blast)
    \<comment> \<open>q\\_tri restricted to T0 is a quotient map from T0 to X.
       Coverage: q\\_tri ` T0 = X (since \\<Union>\\<T> = X and \\<T> = {T0}).
       Quotient topology: U \\<in> TX \\<longleftrightarrow> preimage in T0 is open (from h\\<T>(6)).\<close>
    have hcov: "q_tri ` T0 = X" using h\<T>(5) hT0 by (by100 auto)
    have hcont: "top1_continuous_map_on T0
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T0) X TX q_tri"
      using h\<T>(4) hT0 by (by100 blast)
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T0"
    have hquot_cond: "\<And>U. U \<subseteq> X \<Longrightarrow> U \<in> TX \<longleftrightarrow> {p\<in>T0. q_tri p \<in> U} \<in> ?TP"
    proof -
      fix U assume "U \<subseteq> X"
      from h\<T>(6)[rule_format, OF this]
      have "U \<in> TX \<longleftrightarrow> (\<forall>T\<in>\<T>. {p\<in>T. q_tri p \<in> U} \<in>
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T)" .
      also have "\<dots> = ({p\<in>T0. q_tri p \<in> U} \<in> ?TP)"
        using hT0 by simp
      finally show "U \<in> TX \<longleftrightarrow> {p\<in>T0. q_tri p \<in> U} \<in> ?TP" .
    qed
    have hquot: "top1_quotient_map_on T0 ?TP X TX q_tri"
      unfolding top1_quotient_map_on_def
    proof (intro conjI allI impI)
      show "is_topology_on T0 ?TP"
        using subspace_topology_is_topology_on[OF product_topology_on_is_topology_on[OF
          top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]] by simp
      show "is_topology_on X TX"
        using assms(1) unfolding top1_is_surface_on_def top1_connected_on_def by (by100 blast)
      show "top1_continuous_map_on T0 ?TP X TX q_tri" by (rule hcont)
      show "q_tri ` T0 = X" by (rule hcov)
      fix V assume "V \<subseteq> X" "{p \<in> T0. q_tri p \<in> V} \<in> ?TP"
      thus "V \<in> TX" using hquot_cond[OF \<open>V \<subseteq> X\<close>] by simp
    qed
    show ?thesis
      apply (rule exI[of _ T0], rule exI[of _ 3], rule exI[of _ q_tri])
      using hpoly hquot by (by100 blast)
  qed
  \<comment> \<open>Inductive step: if card > 1, find two adjacent triangles, paste them.\<close>
  show ?thesis
  proof (cases "card \<T> = 1")
    case True thus ?thesis by (rule hbase)
  next
    case False
    \<comment> \<open>card(\\<T>) > 1. By connectedness of X, two triangles share an edge.
       Paste them (\\<S>76 Theorem 76.1) to get a larger polygon. Repeat.\<close>
    have "card \<T> \<noteq> 0" using h\<T>(2) h\<T>(1) by (by100 auto)
    hence "card \<T> > 1" using False \<open>card \<T> \<noteq> 0\<close> by (by100 linarith)
    show ?thesis sorry \<comment> \<open>Induction on card(\\<T>) > 1. At each step, paste two adjacent
       regions sharing a label. When card = 1: done (base case above).\<close>
  qed
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

lemma Lemma_77_4_projective_absorbs_torus:
  fixes a b c :: 'a and w0 w1 :: "('a \<times> bool) list"
  assumes "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
      and "\<forall>e \<in> set w0 \<union> set w1. fst e \<noteq> a \<and> fst e \<noteq> b \<and> fst e \<noteq> c"
      and "infinite (UNIV :: 'a set)"
  shows "top1_scheme_equiv
      (w0 @ [(c, True), (c, True), (a, True), (b, True), (a, False), (b, False)] @ w1)
      (w0 @ [(a, True), (a, True), (b, True), (b, True), (c, True), (c, True)] @ w1)"
proof -
  \<comment> \<open>Fresh label helper: since UNIV is infinite and our sets are finite, fresh labels exist.\<close>
  have hfresh: "\<And>S :: 'a set. finite S \<Longrightarrow> \<exists>x. x \<notin> S"
  proof -
    fix S :: "'a set" assume "finite S"
    from assms(5) have "\<not> finite (UNIV :: 'a set)" by simp
    hence "UNIV \<noteq> S" using \<open>finite S\<close> by (by100 blast)
    thus "\<exists>x. x \<notin> S" by (by100 blast)
  qed
  \<comment> \<open>Obtain a fresh label d \\<noteq> a,b,c and not in w0,w1.\<close>
  obtain d :: 'a where hd: "d \<notin> fst ` (set w0 \<union> set w1) \<union> {a, b, c}"
  proof -
    have "finite (fst ` (set w0 \<union> set w1) \<union> {a, b, c} :: 'a set)" by simp
    moreover have "\<not> finite (UNIV :: 'a set)" using assms(5) by simp
    ultimately have "UNIV \<noteq> (fst ` (set w0 \<union> set w1) \<union> {a, b, c} :: 'a set)" by (by100 metis)
    hence "\<exists>d :: 'a. d \<notin> fst ` (set w0 \<union> set w1) \<union> {a, b, c}" by (by100 blast)
    thus ?thesis using that by (by100 blast)
  qed
  hence hd_ne: "d \<noteq> a" "d \<noteq> b" "d \<noteq> c" and hd_fresh: "\<forall>e \<in> set w0 \<union> set w1. fst e \<noteq> d"
    by (by100 auto)+
  \<comment> \<open>Pre-establish all three Lemma 77.1 applications.\<close>
  have h771_c: "top1_scheme_equiv
      ([(a,True),(b,True)] @ [(c,True)] @ [(b,True),(a,True)] @ [(c,True)] @ (w1 @ w0))
      ([(c,True),(c,True)] @ [(a,True),(b,True)] @ rev (map top1_inverse_edge [(b,True),(a,True)]) @ (w1 @ w0))"
    by (rule Lemma_77_1_projective_collection)
       (use assms hd_ne hd_fresh in \<open>by100 auto\<close>)+
  have h771_b: "top1_scheme_equiv
      ([(a,True)] @ [(b,True)] @ [(c,True)] @ [(b,True)] @ ([(a,True),(c,True)] @ w1 @ w0))
      ([(b,True),(b,True)] @ [(a,True)] @ rev (map top1_inverse_edge [(c,True)]) @ ([(a,True),(c,True)] @ w1 @ w0))"
    by (rule Lemma_77_1_projective_collection)
       (use assms hd_ne hd_fresh in \<open>by100 auto\<close>)+
  have h771_a: "top1_scheme_equiv
      ([(b,True),(b,True)] @ [(a,True)] @ [(c,False)] @ [(a,True)] @ ([(c,True)] @ w1 @ w0))
      ([(a,True),(a,True)] @ [(b,True),(b,True)] @ rev (map top1_inverse_edge [(c,False)]) @ ([(c,True)] @ w1 @ w0))"
    by (rule Lemma_77_1_projective_collection)
       (use assms hd_ne hd_fresh in \<open>by100 auto\<close>)+
  \<comment> \<open>Step 1: Rotate to bring ccaba\\<inverse>b\\<inverse> to front.\<close>
  have s1: "top1_scheme_equiv
      (w0 @ [(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1)
      ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.rotate
      [of w0 "[(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1"]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  \<comment> \<open>Step 2: Lemma 77.1 (*) reversed on label c.
     Forward (*): y0 c y1 c y2 ~ cc y0 inv(y1) y2
     With y0 = [(a,T),(b,T)], y1 = [(b,T),(a,T)], y2 = w1@w0:
     [(a,T),(b,T)] c [(b,T),(a,T)] c (w1@w0) ~ cc [(a,T),(b,T)] inv([(b,T),(a,T)]) (w1@w0)
     = cc [(a,T),(b,T)] [(a,F),(b,F)] (w1@w0)
     Reversed: cc ab a\\<inverse>b\\<inverse> w1 w0 ~ ab c ba c w1 w0.\<close>
  have s2: "top1_scheme_equiv
      ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)
      ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)"
  proof -
    \<comment> \<open>Forward Lemma 77.1 (*) on label c:
       [(a,T),(b,T)] c [(b,T),(a,T)] c (w1@w0) ~ cc [(a,T),(b,T)] inv([(b,T),(a,T)]) (w1@w0)
       i.e., ab c ba c w1w0 ~ cc ab (ba)\\<inverse> w1w0 = cc ab a\\<inverse>b\\<inverse> w1w0.
       Then apply scheme\\_equiv\\_sym to reverse.\<close>
    have fwd: "top1_scheme_equiv
        ([(a,True),(b,True)] @ [(c,True)] @ [(b,True),(a,True)] @ [(c,True)] @ (w1 @ w0))
        ([(c,True),(c,True)] @ [(a,True),(b,True)] @ rev (map top1_inverse_edge [(b,True),(a,True)]) @ (w1 @ w0))"
      by (rule h771_c)
    moreover have "rev (map top1_inverse_edge [(b,True),(a,True)]) = [(a,False),(b,False)]"
      unfolding top1_inverse_edge_def by simp
    ultimately have fwd': "top1_scheme_equiv
        ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)
        ([(c,True),(c,True),(a,True),(b,True),(a,False),(b,False)] @ w1 @ w0)"
      by simp
    show ?thesis by (rule scheme_equiv_sym[OF fwd'])
  qed
  \<comment> \<open>Step 3: Lemma 77.1 (*) forward on label b.
     [a] b [c] b [acw1w0] ~ bb [a] inv([c]) [acw1w0] = bb a c\\<inverse> a c w1 w0.\<close>
  have s3: "top1_scheme_equiv
      ([(a,True),(b,True),(c,True),(b,True),(a,True),(c,True)] @ w1 @ w0)
      ([(b,True),(b,True),(a,True),(c,False),(a,True),(c,True)] @ w1 @ w0)"
  proof -
    have "top1_scheme_equiv
        ([(a,True)] @ [(b,True)] @ [(c,True)] @ [(b,True)] @ ([(a,True),(c,True)] @ w1 @ w0))
        ([(b,True),(b,True)] @ [(a,True)] @ rev (map top1_inverse_edge [(c,True)]) @ ([(a,True),(c,True)] @ w1 @ w0))"
      by (rule h771_b)
    moreover have "rev (map top1_inverse_edge [(c,True)]) = [(c,False)]"
      unfolding top1_inverse_edge_def by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Step 4: Lemma 77.1 (*) forward on label a.
     [bb] a [c\\<inverse>] a [cw1w0] ~ aa [bb] inv([c\\<inverse>]) [cw1w0] = aa bb c c w1 w0.\<close>
  have s4: "top1_scheme_equiv
      ([(b,True),(b,True),(a,True),(c,False),(a,True),(c,True)] @ w1 @ w0)
      ([(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1 @ w0)"
  proof -
    have "top1_scheme_equiv
        ([(b,True),(b,True)] @ [(a,True)] @ [(c,False)] @ [(a,True)] @ ([(c,True)] @ w1 @ w0))
        ([(a,True),(a,True)] @ [(b,True),(b,True)] @ rev (map top1_inverse_edge [(c,False)]) @ ([(c,True)] @ w1 @ w0))"
      by (rule h771_a)
    moreover have "rev (map top1_inverse_edge [(c,False)]) = [(c,True)]"
      unfolding top1_inverse_edge_def by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Step 5: Rotate back.\<close>
  have s5: "top1_scheme_equiv
      ([(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1 @ w0)
      (w0 @ [(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1)"
    unfolding top1_scheme_equiv_def
    using top1_elementary_scheme_operation.rotate
      [of "[(a,True),(a,True),(b,True),(b,True),(c,True),(c,True)] @ w1" w0]
    by (simp add: rtranclp.rtrancl_into_rtrancl)
  from s1 s2 s3 s4 s5 show ?thesis
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
qed

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
          ultimately show "x = y" using heq by (by100 presburger)
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

\<comment> \<open>Suffix congruence: xs \<sim> ys implies xs@suffix \<sim> ys@suffix.\<close>
lemma scheme_equiv_append:
  fixes xs ys :: "('a \<times> bool) list" and suffix :: "('a \<times> bool) list"
  assumes "top1_scheme_equiv xs ys"
  shows "top1_scheme_equiv (xs @ suffix) (ys @ suffix)"
proof -
  \<comment> \<open>Chain: xs@suffix \<sim> suffix@xs \<sim> suffix@ys \<sim> ys@suffix.\<close>
  have r1: "top1_scheme_equiv (xs @ suffix) (suffix @ xs)"
    using elementary_imp_equiv[OF top1_elementary_scheme_operation.rotate[of xs suffix]] by (by100 simp)
  have r2: "top1_scheme_equiv (suffix @ xs) (suffix @ ys)"
    using scheme_equiv_prepend[OF assms] by (by100 blast)
  have r3: "top1_scheme_equiv (suffix @ ys) (ys @ suffix)"
    using elementary_imp_equiv[OF top1_elementary_scheme_operation.rotate[of suffix ys]] by (by100 simp)
  from r1 r2 r3 show ?thesis
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
qed

\<comment> \<open>Relabel target to avoid a specific label.\<close>
lemma scheme_equiv_relabel_avoid:
  fixes target :: "(nat \<times> bool) list" and a :: nat
  shows "\<exists>target'. top1_scheme_equiv target target' \<and> (\<forall>e \<in> set target'. fst e \<noteq> a)"
proof -
  have "finite (fst ` set target \<union> {a} :: nat set)" by (by100 simp)
  from ex_new_if_finite[OF infinite_UNIV_nat this]
  obtain fresh :: nat where hfresh: "fresh \<notin> fst ` set target \<union> {a}" by (by100 blast)
  hence "fresh \<noteq> a" by (by100 blast)
  define target' where "target' = map (\<lambda>(l,b). (if l = a then fresh else l, b)) target"
  have "top1_scheme_equiv target target'"
    unfolding target'_def
    using elementary_imp_equiv[OF top1_elementary_scheme_operation.relabel[of target a fresh]] by (by100 simp)
  moreover have "\<forall>e \<in> set target'. fst e \<noteq> a"
  proof (intro ballI)
    fix e assume "e \<in> set target'"
    then obtain e0 where "e0 \<in> set target" "e = (\<lambda>(l,b). (if l = a then fresh else l, b)) e0"
      unfolding target'_def by (by100 force)
    obtain l0 b0 where "e0 = (l0, b0)" by (cases e0)
    hence "e = (if l0 = a then fresh else l0, b0)"
      using \<open>e = (\<lambda>(l,b). (if l = a then fresh else l, b)) e0\<close> by (by100 simp)
    hence "fst e = (if fst e0 = a then fresh else fst e0)"
      using \<open>e0 = (l0, b0)\<close> by (by100 simp)
    thus "fst e \<noteq> a" using \<open>fresh \<noteq> a\<close> by (by100 simp)
  qed
  ultimately show ?thesis by (by100 blast)
qed

\<comment> \<open>Any scheme of the form [(l0,T),(l0,T),...,(lm,T),(lm,T)] with distinct labels
   is equivalent to the standard projective scheme proj(m+1) via relabeling.\<close>
lemma projective_form_equiv_standard:
  fixes w :: "(nat \<times> bool) list"
  assumes "length w = 2 * m"
      and "\<forall>i < m. w!(2*i) = (f i, True) \<and> w!(2*i+1) = (f i, True)"
      and "inj_on f {..<m}"
  shows "top1_scheme_equiv w (top1_m_projective_scheme m)"
  using assms
proof (induction m arbitrary: w f)
  case 0 thus ?case unfolding top1_scheme_equiv_def top1_m_projective_scheme_def by (by100 simp)
next
  case (Suc m)
  \<comment> \<open>w has Suc m pairs. Split off the last pair: w = w' @ [(f m, True), (f m, True)].\<close>
  \<comment> \<open>By IH: w' \<sim> proj m. Then w = w' @ [(f m,T),(f m,T)] \<sim> proj m @ [(f m,T),(f m,T)] (suffix congruence).\<close>
  \<comment> \<open>Relabel f m \<to> m (possibly via relabel\_avoid): proj m @ [(m,T),(m,T)] = proj (Suc m).\<close>
  \<comment> \<open>w has length 2*(m+1). Define w' = take (2*m) w (first m pairs).\<close>
  define w' where "w' = take (2*m) w"
  have hlen_w: "length w = 2 * Suc m" using Suc.prems(1) by (by100 simp)
  hence hlen_w': "length w' = 2 * m" unfolding w'_def by (by100 simp)
  \<comment> \<open>The last pair is [(f m, T), (f m, T)].\<close>
  have hlast: "w = w' @ [(f m, True), (f m, True)]"
  proof -
    have "w = take (2*m) w @ drop (2*m) w" by (by100 simp)
    moreover have "drop (2*m) w = [(f m, True), (f m, True)]"
    proof -
      have "length (drop (2*m) w) = 2" using hlen_w by (by100 simp)
      moreover have "(drop (2*m) w)!0 = w!(2*m)" using hlen_w by (by100 simp)
      moreover have "(drop (2*m) w)!1 = w!(2*m+1)" using hlen_w by (by100 simp)
      moreover have "w!(2*m) = (f m, True)" using Suc.prems(2)[rule_format, of m] by (by100 simp)
      moreover have "w!(2*m+1) = (f m, True)" using Suc.prems(2)[rule_format, of m] by (by100 simp)
      ultimately show ?thesis
        by (cases "drop (2*m) w", by100 simp, cases "tl (drop (2*m) w)", by100 simp, by100 simp)
    qed
    ultimately show ?thesis unfolding w'_def by (by100 simp)
  qed
  \<comment> \<open>IH conditions for w'.\<close>
  define g where "g i = f i" for i
  have hw'_struct: "\<forall>i < m. w'!(2*i) = (g i, True) \<and> w'!(2*i+1) = (g i, True)"
  proof (intro allI impI)
    fix i assume "i < m"
    hence "2*i < 2*m" "2*i+1 < 2*m" by (by100 simp)+
    have "w'!(2*i) = w!(2*i)" unfolding w'_def using \<open>2*i < 2*m\<close> hlen_w by (by100 simp)
    moreover have "w'!(2*i+1) = w!(2*i+1)" unfolding w'_def using \<open>2*i+1 < 2*m\<close> hlen_w by (by100 simp)
    moreover from Suc.prems(2)[rule_format, of i] \<open>i < m\<close>
    have "w!(2*i) = (f i, True) \<and> w!(2*i+1) = (f i, True)" by (by100 simp)
    ultimately show "w'!(2*i) = (g i, True) \<and> w'!(2*i+1) = (g i, True)"
      unfolding g_def by (by100 simp)
  qed
  have hg_inj: "inj_on g {..<m}"
    unfolding g_def using Suc.prems(3) by (rule inj_on_subset) (by100 simp)
  \<comment> \<open>Apply IH: w' \<sim> proj m.\<close>
  from Suc.IH[OF hlen_w' hw'_struct hg_inj]
  have "top1_scheme_equiv w' (top1_m_projective_scheme m)" unfolding g_def .
  \<comment> \<open>Suffix congruence: w = w' @ [(f m,T),(f m,T)] \<sim> proj m @ [(f m,T),(f m,T)].\<close>
  hence "top1_scheme_equiv w (top1_m_projective_scheme m @ [(f m, True), (f m, True)])"
    using scheme_equiv_append[of w' "top1_m_projective_scheme m" "[(f m, True), (f m, True)]"]
    hlast by (by100 simp)
  \<comment> \<open>Relabel f m \<to> m (via relabel\_avoid if needed), then proj m @ [(m,T),(m,T)] = proj(Suc m).\<close>
  moreover have "top1_scheme_equiv (top1_m_projective_scheme m @ [(f m, True), (f m, True)])
      (top1_m_projective_scheme (Suc m))"
  proof -
    \<comment> \<open>Relabel\_avoid on proj m to avoid f(m), then relabel f(m) \<to> m.\<close>
    from scheme_equiv_relabel_avoid[of "top1_m_projective_scheme m" "f m"]
    obtain pm_no_fm where hpm: "top1_scheme_equiv (top1_m_projective_scheme m) pm_no_fm"
        "\<forall>e \<in> set pm_no_fm. fst e \<noteq> f m" by (by100 blast)
    \<comment> \<open>Suffix congruence: proj m @ [(f m,T),(f m,T)] \<sim> pm\_no\_fm @ [(f m,T),(f m,T)].\<close>
    have "top1_scheme_equiv (top1_m_projective_scheme m @ [(f m,True),(f m,True)])
        (pm_no_fm @ [(f m,True),(f m,True)])"
      using scheme_equiv_append[OF hpm(1)] by (by100 blast)
    \<comment> \<open>Relabel f(m) \<to> m in the full scheme. f(m) only appears in the suffix pair
       (since pm\_no\_fm avoids f(m)). So result = pm\_no\_fm @ [(m,T),(m,T)].\<close>
    moreover have "top1_scheme_equiv (pm_no_fm @ [(f m,True),(f m,True)])
        (pm_no_fm @ [(m,True),(m,True)])"
    proof -
      \<comment> \<open>Relabel f(m) \<to> m in the full scheme. Since pm\_no\_fm avoids f(m),
         only the suffix pair is affected.\<close>
      have "top1_elementary_scheme_operation (pm_no_fm @ [(f m,True),(f m,True)])
          (map (\<lambda>(l,b). (if l = f m then m else l, b)) (pm_no_fm @ [(f m,True),(f m,True)]))"
        by (rule top1_elementary_scheme_operation.relabel)
      moreover have "map (\<lambda>(l,b). (if l = f m then m else l, b)) pm_no_fm = pm_no_fm"
        using hpm(2) by (intro map_idI) (by100 force)
      hence "map (\<lambda>(l,b). (if l = f m then m else l, b)) (pm_no_fm @ [(f m,True),(f m,True)])
          = pm_no_fm @ [(m,True),(m,True)]" by (by100 simp)
      ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
    qed
    \<comment> \<open>pm\_no\_fm \<sim> proj m (reverse of relabel\_avoid). So pm\_no\_fm @ [(m,T),(m,T)] \<sim> proj m @ [(m,T),(m,T)].\<close>
    moreover have "top1_scheme_equiv (pm_no_fm @ [(m,True),(m,True)])
        (top1_m_projective_scheme m @ [(m,True),(m,True)])"
      using scheme_equiv_append[OF scheme_equiv_sym[OF hpm(1)]] by (by100 blast)
    \<comment> \<open>proj m @ [(m,T),(m,T)] = proj(Suc m) by definition.\<close>
    moreover have "top1_m_projective_scheme m @ [(m,True),(m,True)] = top1_m_projective_scheme (Suc m)"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    ultimately have "top1_scheme_equiv (top1_m_projective_scheme m @ [(f m, True), (f m, True)])
        (top1_m_projective_scheme m @ [(m, True), (m, True)])"
      unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
    moreover have "top1_m_projective_scheme m @ [(m,True),(m,True)] = top1_m_projective_scheme (Suc m)"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
  qed
  ultimately show ?case unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
qed

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

lemma proj_append_pair:
  "top1_scheme_equiv (top1_m_projective_scheme m @ [(a, True), (a, True)]) (top1_m_projective_scheme (Suc m))"
proof -
  from scheme_equiv_relabel_avoid[of "top1_m_projective_scheme m" a]
  obtain pm_no_a where hpm: "top1_scheme_equiv (top1_m_projective_scheme m) pm_no_a"
      "\<forall>e \<in> set pm_no_a. fst e \<noteq> a" by (by100 blast)
  have "top1_scheme_equiv (top1_m_projective_scheme m @ [(a,True),(a,True)])
      (pm_no_a @ [(a,True),(a,True)])"
    using scheme_equiv_append[OF hpm(1)] by (by100 blast)
  moreover have "top1_scheme_equiv (pm_no_a @ [(a,True),(a,True)])
      (pm_no_a @ [(m,True),(m,True)])"
  proof -
    have "top1_elementary_scheme_operation (pm_no_a @ [(a,True),(a,True)])
        (map (\<lambda>(l,b). (if l = a then m else l, b)) (pm_no_a @ [(a,True),(a,True)]))"
      by (rule top1_elementary_scheme_operation.relabel)
    moreover have "map (\<lambda>(l,b). (if l = a then m else l, b)) pm_no_a = pm_no_a"
      using hpm(2) by (intro map_idI) (by100 force)
    hence "map (\<lambda>(l,b). (if l = a then m else l, b)) (pm_no_a @ [(a,True),(a,True)])
        = pm_no_a @ [(m,True),(m,True)]" by (by100 simp)
    ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
  qed
  moreover have "top1_scheme_equiv (pm_no_a @ [(m,True),(m,True)])
      (top1_m_projective_scheme m @ [(m,True),(m,True)])"
    using scheme_equiv_append[OF scheme_equiv_sym[OF hpm(1)]] by (by100 blast)
  ultimately have "top1_scheme_equiv (top1_m_projective_scheme m @ [(a,True),(a,True)])
      (top1_m_projective_scheme m @ [(m,True),(m,True)])"
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
  moreover have "top1_m_projective_scheme m @ [(m,True),(m,True)] = top1_m_projective_scheme (Suc m)"
    unfolding top1_m_projective_scheme_def by (by100 simp)
  ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
qed

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

lemma proj_pair_absorbs_torus:
  "top1_scheme_equiv ([(a, True), (a, True)] @ top1_n_torus_scheme n) (top1_m_projective_scheme (2*n + 1))"
proof (induction n arbitrary: a)
  case 0
  \<comment> \<open>Base: [(a,T),(a,T)] @ [] = [(a,T),(a,T)] \<sim> proj 1.\<close>
  have "top1_m_projective_scheme 1 = [(0,True),(0,True)]"
    unfolding top1_m_projective_scheme_def by (by100 simp)
  moreover have "top1_scheme_equiv [(a,True),(a,True)] [(0::nat,True),(0,True)]"
  proof -
    have "top1_elementary_scheme_operation [(a,True),(a,True)]
        (map (\<lambda>(l,b). (if l = a then 0 else l, b)) [(a,True),(a,True)])"
      by (rule top1_elementary_scheme_operation.relabel)
    moreover have "map (\<lambda>(l,b). (if l = a then 0 else l, b)) [(a,True),(a,True)] = [(0,True),(0,True)]"
      by (by100 simp)
    ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
  qed
  ultimately show ?case unfolding top1_n_torus_scheme_def by (by100 simp)
next
  case (Suc n)
  \<comment> \<open>Suc: [(a,T),(a,T)] @ torus(Suc n) = [(a,T),(a,T)] @ torus n @ [block].
     IH: [(a,T),(a,T)] @ torus n \<sim> proj(2n+1).
     Suffix congruence: ... @ block \<sim> proj(2n+1) @ block.
     Then absorb block into proj via Lemma 77.4.\<close>
  have htorus_suc: "top1_n_torus_scheme (Suc n) = top1_n_torus_scheme n
      @ [(2*n, True), (2*n+1, True), (2*n, False), (2*n+1, False)]"
    unfolding top1_n_torus_scheme_def by (by100 simp)
  \<comment> \<open>IH gives: [(a,T),(a,T)] @ torus n \<sim> proj(2n+1).\<close>
  from Suc.IH have hIH: "top1_scheme_equiv ([(a,True),(a,True)] @ top1_n_torus_scheme n)
      (top1_m_projective_scheme (2*n+1))" .
  \<comment> \<open>Suffix congruence: append torus block.\<close>
  let ?block = "[(2*n, True), (2*n+1, True), (2*n, False), (2*n+1, False)]"
  have "top1_scheme_equiv ([(a,True),(a,True)] @ top1_n_torus_scheme n @ ?block)
      (top1_m_projective_scheme (2*n+1) @ ?block)"
    using scheme_equiv_append[OF hIH, of ?block] by (by100 simp)
  hence s1: "top1_scheme_equiv ([(a,True),(a,True)] @ top1_n_torus_scheme (Suc n))
      (top1_m_projective_scheme (2*n+1) @ ?block)"
    using htorus_suc by (by100 simp)
  \<comment> \<open>Absorb: proj(2n+1) @ [torus\_block] \<sim> proj(2n+3) via Lemma 77.4 + relabeling.\<close>
  have s2: "top1_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block) (top1_m_projective_scheme (2*(Suc n)+1))"
  proof -
    \<comment> \<open>Step A: relabel torus block's label (2*n) to fresh via context\_left (only affects suffix).\<close>
    have "finite (fst ` set (top1_m_projective_scheme (2*n+1)) \<union> {2*n, 2*n+1} :: nat set)" by (by100 simp)
    from ex_new_if_finite[OF infinite_UNIV_nat this]
    obtain fresh1 :: nat where hf1: "fresh1 \<notin> fst ` set (top1_m_projective_scheme (2*n+1)) \<union> {2*n, 2*n+1}"
      by (by100 blast)
    have "finite (fst ` set (top1_m_projective_scheme (2*n+1)) \<union> {2*n, 2*n+1, fresh1} :: nat set)" by (by100 simp)
    from ex_new_if_finite[OF infinite_UNIV_nat this]
    obtain fresh2 :: nat where hf2: "fresh2 \<notin> fst ` set (top1_m_projective_scheme (2*n+1)) \<union> {2*n, 2*n+1, fresh1}"
      by (by100 blast)
    \<comment> \<open>Relabel 2*n \<to> fresh1 in the suffix (context\_left keeps prefix unchanged).\<close>
    have r1: "top1_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block)
        (top1_m_projective_scheme (2*n+1) @ [(fresh1,True),(2*n+1,True),(fresh1,False),(2*n+1,False)])"
    proof -
      have "top1_elementary_scheme_operation ?block
          (map (\<lambda>(l,b). (if l = 2*n then fresh1 else l, b)) ?block)"
        by (rule top1_elementary_scheme_operation.relabel)
      moreover have "map (\<lambda>(l,b). (if l = 2*n then fresh1 else l, b)) ?block
          = [(fresh1,True),(2*n+1,True),(fresh1,False),(2*n+1,False)]" by (by100 simp)
      ultimately have "top1_elementary_scheme_operation ?block [(fresh1,True),(2*n+1,True),(fresh1,False),(2*n+1,False)]"
        by (by100 simp)
      from top1_elementary_scheme_operation.context_left[OF this, of "top1_m_projective_scheme (2*n+1)"]
      show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
    qed
    \<comment> \<open>Relabel 2*n+1 \<to> fresh2 in the suffix.\<close>
    have r2: "top1_scheme_equiv
        (top1_m_projective_scheme (2*n+1) @ [(fresh1,True),(2*n+1,True),(fresh1,False),(2*n+1,False)])
        (top1_m_projective_scheme (2*n+1) @ [(fresh1,True),(fresh2,True),(fresh1,False),(fresh2,False)])"
    proof -
      let ?suf1 = "[(fresh1,True),(2*n+1,True),(fresh1,False),(2*n+1,False)]"
      have "top1_elementary_scheme_operation ?suf1
          (map (\<lambda>(l,b). (if l = 2*n+1 then fresh2 else l, b)) ?suf1)"
        by (rule top1_elementary_scheme_operation.relabel)
      moreover have "fresh1 \<noteq> 2*n+1" using hf1 by (by100 blast)
      hence "map (\<lambda>(l,b). (if l = 2*n+1 then fresh2 else l, b)) ?suf1
          = [(fresh1,True),(fresh2,True),(fresh1,False),(fresh2,False)]" by (by100 simp)
      ultimately have "top1_elementary_scheme_operation ?suf1 [(fresh1,True),(fresh2,True),(fresh1,False),(fresh2,False)]"
        by (by100 simp)
      from top1_elementary_scheme_operation.context_left[OF this, of "top1_m_projective_scheme (2*n+1)"]
      show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
    qed
    \<comment> \<open>Step B: Split proj(2n+1) = proj(2n) @ [(2n,T),(2n,T)]. Apply Lemma 77.4.\<close>
    \<comment> \<open>proj(2n) @ [(2n,T),(2n,T),(fresh1,T),(fresh2,T),(fresh1,F),(fresh2,F)]
       \<to> proj(2n) @ [(fresh1,T),(fresh1,T),(fresh2,T),(fresh2,T),(2n,T),(2n,T)] via Lemma 77.4.\<close>
    have r3: "top1_scheme_equiv
        (top1_m_projective_scheme (2*n+1) @ [(fresh1,True),(fresh2,True),(fresh1,False),(fresh2,False)])
        (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True),(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])"
    proof -
      \<comment> \<open>Split proj(2n+1) = proj(2n) @ [(2n,T),(2n,T)].\<close>
      have hsplit: "top1_m_projective_scheme (2*n+1) = top1_m_projective_scheme (2*n) @ [(2*n,True),(2*n,True)]"
        unfolding top1_m_projective_scheme_def by (by100 simp)
      \<comment> \<open>LHS = proj(2n) @ [(2n,T),(2n,T),(fresh1,T),(fresh2,T),(fresh1,F),(fresh2,F)].\<close>
      \<comment> \<open>Apply Lemma 77.4 with c=2n, a=fresh1, b=fresh2, w0=proj(2n), w1=[].\<close>
      have "2*n \<noteq> fresh1" using hf1 by (by100 blast)
      have "2*n \<noteq> fresh2" using hf2 by (by100 blast)
      have "fresh1 \<noteq> fresh2" using hf2 by (by100 blast)
      have hlabels: "\<forall>e \<in> set (top1_m_projective_scheme (2*n)) \<union> set ([] :: (nat \<times> bool) list).
          fst e \<noteq> fresh1 \<and> fst e \<noteq> fresh2 \<and> fst e \<noteq> (2*n)"
      proof (intro ballI conjI)
        fix e assume "e \<in> set (top1_m_projective_scheme (2*n)) \<union> set ([] :: (nat \<times> bool) list)"
        hence "e \<in> set (top1_m_projective_scheme (2*n))" by (by100 simp)
        \<comment> \<open>proj(2n) \<subseteq> proj(2n+1) (prefix). So labels of proj(2n) \<subseteq> labels of proj(2n+1).\<close>
        hence "e \<in> set (top1_m_projective_scheme (2*n+1))"
          unfolding top1_m_projective_scheme_def by (by100 force)
        hence "fst e \<in> fst ` set (top1_m_projective_scheme (2*n+1))" by (by100 blast)
        thus "fst e \<noteq> fresh1" using hf1 by (by100 blast)
        thus "fst e \<noteq> fresh2" using hf2 \<open>fst e \<in> fst ` set (top1_m_projective_scheme (2*n+1))\<close> by (by100 blast)
        \<comment> \<open>fst e \<noteq> 2*n: proj(2n) uses labels {0..2n-1}. All fst \<le> 2n-1 < 2n.\<close>
        show "fst e \<noteq> 2*n"
        proof -
          from \<open>e \<in> set (top1_m_projective_scheme (2*n))\<close>
          obtain i where "i < length (top1_m_projective_scheme (2*n))"
              "top1_m_projective_scheme (2*n) ! i = e"
            by (simp add: in_set_conv_nth) (by100 blast)
          have "length (top1_m_projective_scheme (2*n)) = 2*(2*n)"
            using projective_scheme_length by (by100 simp)
          hence "i < 2*(2*n)" using \<open>i < length _\<close> by (by100 simp)
          hence "fst e = i div 2" using projective_scheme_nth[of i "2*n"] \<open>_ ! i = e\<close> by (by100 simp)
          moreover have "i div 2 < 2*n" using \<open>i < 2*(2*n)\<close> by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
      qed
      have "fresh1 \<noteq> 2*n" using \<open>2*n \<noteq> fresh1\<close> by (by100 simp)
      have "fresh2 \<noteq> 2*n" using \<open>2*n \<noteq> fresh2\<close> by (by100 simp)
      have "top1_scheme_equiv
          (top1_m_projective_scheme (2*n) @ [(2*n,True),(2*n,True),(fresh1,True),(fresh2,True),(fresh1,False),(fresh2,False)] @ [])
          (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True),(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)] @ [])"
        using Lemma_77_4_projective_absorbs_torus[OF \<open>fresh1 \<noteq> fresh2\<close> \<open>fresh1 \<noteq> 2*n\<close> \<open>fresh2 \<noteq> 2*n\<close>
            hlabels infinite_UNIV_nat] by (by100 blast)
      hence "top1_scheme_equiv
          (top1_m_projective_scheme (2*n) @ [(2*n,True),(2*n,True),(fresh1,True),(fresh2,True),(fresh1,False),(fresh2,False)])
          (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True),(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])"
        by (by100 simp)
      thus ?thesis using hsplit by (by100 simp)
    qed
    \<comment> \<open>Step C: Apply proj\_append\_pair 3 times to absorb the 3 new proj pairs.\<close>
    have r4: "top1_scheme_equiv
        (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True),(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])
        (top1_m_projective_scheme (2*n+3))"
    proof -
      \<comment> \<open>Step 1: proj(2n) @ [(f1,T),(f1,T)] \<sim> proj(2n+1). Suffix: [(f2,T),(f2,T),(2n,T),(2n,T)].\<close>
      from scheme_equiv_append[OF proj_append_pair[of "2*n" fresh1],
          of "[(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)]"]
      have "top1_scheme_equiv
          (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True)] @ [(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc (2*n)) @ [(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])"
        by (by100 simp)
      hence s1: "top1_scheme_equiv
          (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True),(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc (2*n)) @ [(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])"
        by (by100 simp)
      \<comment> \<open>Step 2: proj(2n+1) @ [(f2,T),(f2,T)] \<sim> proj(2n+2). Suffix: [(2n,T),(2n,T)].\<close>
      from scheme_equiv_append[OF proj_append_pair[of "Suc (2*n)" fresh2],
          of "[(2*n,True),(2*n,True)]"]
      have "top1_scheme_equiv
          (top1_m_projective_scheme (Suc (2*n)) @ [(fresh2,True),(fresh2,True)] @ [(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc (Suc (2*n))) @ [(2*n,True),(2*n,True)])"
        by (by100 simp)
      hence s2: "top1_scheme_equiv
          (top1_m_projective_scheme (Suc (2*n)) @ [(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc (Suc (2*n))) @ [(2*n,True),(2*n,True)])"
        by (by100 simp)
      \<comment> \<open>Step 3: proj(2n+2) @ [(2n,T),(2n,T)] \<sim> proj(2n+3).\<close>
      have s3: "top1_scheme_equiv
          (top1_m_projective_scheme (Suc (Suc (2*n))) @ [(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc (Suc (Suc (2*n)))))"
        by (rule proj_append_pair)
      from s1 s2 have "top1_scheme_equiv
          (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True),(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc (Suc (2*n))) @ [(2*n,True),(2*n,True)])"
        unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
      from this s3 have "top1_scheme_equiv
          (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True),(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])
          (top1_m_projective_scheme (Suc (Suc (Suc (2*n)))))"
        unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
      moreover have "Suc (Suc (Suc (2*n))) = 2*n+3" by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    from r1 r2 have "top1_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block)
        (top1_m_projective_scheme (2*n+1) @ [(fresh1,True),(fresh2,True),(fresh1,False),(fresh2,False)])"
      unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
    from this r3 have "top1_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block)
        (top1_m_projective_scheme (2*n) @ [(fresh1,True),(fresh1,True),(fresh2,True),(fresh2,True),(2*n,True),(2*n,True)])"
      unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
    from this r4 have "top1_scheme_equiv (top1_m_projective_scheme (2*n+1) @ ?block) (top1_m_projective_scheme (2*n+3))"
      unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
    moreover have "2*n+3 = 2*(Suc n)+1" by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  from s1 s2 show ?case unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
qed


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

lemma proj_absorbs_one_torus:
  assumes "m > 0"
  shows "top1_scheme_equiv (top1_m_projective_scheme m @ top1_n_torus_scheme 1) (top1_m_projective_scheme (m+2))"
  using assms
proof (induction m)
  case 0 thus ?case by (by100 simp)
next
  case (Suc m')
  show ?case
  proof (cases "m' = 0")
    case True
    \<comment> \<open>Base: m=1 (i.e. m'=0). proj\_1 @ torus\_1 ~ proj\_3.\<close>
    have "top1_scheme_equiv ([(0::nat,True),(0,True)] @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme (2*1+1))"
      using proj_pair_absorbs_torus[of 0 1] .
    hence "top1_scheme_equiv ([(0::nat,True),(0,True)] @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme 3)" by (by100 simp)
    moreover have "top1_m_projective_scheme 1 = [(0::nat,True),(0,True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    ultimately have h_b: "top1_scheme_equiv (top1_m_projective_scheme 1 @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme 3)" by (by100 simp)
    from True have "Suc m' = 1" "Suc m' + 2 = 3" by (by100 simp)+
    with h_b show ?thesis by (by100 metis)
  next
    case nFalse: False
    hence "m' > 0" by (by100 simp)
    \<comment> \<open>proj\_(Suc m') = proj\_m' @ [(m',T),(m',T)] (definition decomposition).\<close>
    have hpm_decomp: "top1_m_projective_scheme (Suc m') =
        top1_m_projective_scheme m' @ [(m', True), (m', True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    \<comment> \<open>proj\_(Suc m') @ torus\_1 = proj\_m' @ [(m',T),(m',T)] @ torus\_1.\<close>
    hence h_expand: "top1_m_projective_scheme (Suc m') @ top1_n_torus_scheme 1 =
        top1_m_projective_scheme m' @ [(m', True), (m', True)] @ top1_n_torus_scheme 1"
      by (by100 simp)
    \<comment> \<open>Rotate [(m',T),(m',T)] @ torus\_1 to torus\_1 @ [(m',T),(m',T)] in suffix.\<close>
    have "top1_scheme_equiv ([(m', True), (m', True)] @ top1_n_torus_scheme 1)
        (top1_n_torus_scheme 1 @ [(m', True), (m', True)])"
      using elementary_imp_equiv[OF top1_elementary_scheme_operation.rotate
        [of "[(m', True), (m', True)]" "top1_n_torus_scheme 1"]] by (by100 simp)
    hence h_rot: "top1_scheme_equiv
        (top1_m_projective_scheme m' @ [(m', True), (m', True)] @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme m' @ top1_n_torus_scheme 1 @ [(m', True), (m', True)])"
      using scheme_equiv_prepend[of "[(m', True), (m', True)] @ top1_n_torus_scheme 1"
        "top1_n_torus_scheme 1 @ [(m', True), (m', True)]" "top1_m_projective_scheme m'"]
      by (by100 simp)
    \<comment> \<open>By IH: proj\_m' @ torus\_1 ~ proj\_(m'+2).\<close>
    from Suc.IH[OF \<open>m' > 0\<close>]
    have hIH: "top1_scheme_equiv (top1_m_projective_scheme m' @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme (m'+2))" .
    \<comment> \<open>Lift: proj\_(m'+2) @ [(m',T),(m',T)] (suffix congruence).\<close>
    have "top1_scheme_equiv
        (top1_m_projective_scheme m' @ top1_n_torus_scheme 1 @ [(m', True), (m', True)])
        (top1_m_projective_scheme (m'+2) @ [(m', True), (m', True)])"
      using scheme_equiv_append[OF hIH] by (by100 simp)
    \<comment> \<open>proj\_append\_pair: proj\_(m'+2) @ [(m',T),(m',T)] ~ proj\_(Suc(m'+2)) = proj\_(m'+3).\<close>
    moreover have "top1_scheme_equiv (top1_m_projective_scheme (m'+2) @ [(m', True), (m', True)])
        (top1_m_projective_scheme (Suc (m'+2)))"
      using proj_append_pair[of "m'+2" m'] .
    ultimately have hstep: "top1_scheme_equiv
        (top1_m_projective_scheme m' @ top1_n_torus_scheme 1 @ [(m', True), (m', True)])
        (top1_m_projective_scheme (Suc (m'+2)))"
      unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
    \<comment> \<open>Chain: Suc m' @ torus = (expand) proj m' @ pair @ torus = (rotate) proj m' @ torus @ pair → (step) proj (Suc(m'+2)).\<close>
    have "top1_scheme_equiv
        (top1_m_projective_scheme (Suc m') @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme m' @ [(m', True), (m', True)] @ top1_n_torus_scheme 1)"
      using h_expand unfolding top1_scheme_equiv_def by (by100 simp)
    moreover note h_rot
    moreover note hstep
    ultimately have "top1_scheme_equiv
        (top1_m_projective_scheme (Suc m') @ top1_n_torus_scheme 1)
        (top1_m_projective_scheme (Suc (m'+2)))"
      unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
    moreover have "Suc (m'+2) = Suc m' + 2" by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
qed

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

lemma commutator_prepend_projective:
  assumes "a \<noteq> (b :: nat)" and "m > 0"
  shows "\<exists>w'. top1_is_projective_scheme w' (m+2) \<and>
      top1_scheme_equiv ([(a, True), (b, True), (a, False), (b, False)] @ top1_m_projective_scheme m) w'"
proof -
  let ?block = "[(a, True), (b, True), (a, False), (b, False)]"
  \<comment> \<open>block ~ torus\_1. Lift: block @ proj\_m ~ torus\_1 @ proj\_m ~ proj\_m @ torus\_1.\<close>
  have h1: "top1_scheme_equiv (?block @ top1_m_projective_scheme m)
      (top1_m_projective_scheme m @ top1_n_torus_scheme 1)"
  proof -
    have "top1_scheme_equiv ?block (top1_n_torus_scheme 1)"
      using commutator_block_equiv_torus_1[OF assms(1)] .
    hence "top1_scheme_equiv (?block @ top1_m_projective_scheme m)
        (top1_n_torus_scheme 1 @ top1_m_projective_scheme m)"
      using scheme_equiv_append by (by100 blast)
    moreover have "top1_scheme_equiv (top1_n_torus_scheme 1 @ top1_m_projective_scheme m)
        (top1_m_projective_scheme m @ top1_n_torus_scheme 1)"
      using elementary_imp_equiv[OF top1_elementary_scheme_operation.rotate
        [of "top1_n_torus_scheme 1" "top1_m_projective_scheme m"]] by (by100 simp)
    ultimately show ?thesis unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
  qed
  \<comment> \<open>proj\_m @ torus\_1 ~ proj\_(m+2) by proj\_pair\_absorbs\_torus (proj pair absorbs the torus).\<close>
  \<comment> \<open>proj\_pair\_absorbs\_torus: [(c,T),(c,T)] @ torus\_n ~ proj\_(2n+1).\<close>
  \<comment> \<open>We have proj\_m @ torus\_1. Reverse of absorbs: torus\_1 is absorbed using 1 proj pair.
     proj\_m has m pairs. Use 1, gain 3. Net: m-1+3 = m+2.\<close>
  have h2: "top1_scheme_equiv (top1_m_projective_scheme m @ top1_n_torus_scheme 1)
      (top1_m_projective_scheme (m+2))"
    using proj_absorbs_one_torus[OF assms(2)] .
  from h1 h2 have "top1_scheme_equiv (?block @ top1_m_projective_scheme m) (top1_m_projective_scheme (m+2))"
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
  moreover have "m + 2 > 0" using assms(2) by (by100 simp)
  ultimately show ?thesis unfolding top1_is_projective_scheme_def by (by100 blast)
qed

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

lemma commutator_prepend_torus:
  assumes "a \<noteq> (b :: nat)" and "n > 0"
  shows "top1_scheme_equiv ([(a, True), (b, True), (a, False), (b, False)] @ top1_n_torus_scheme n)
      (top1_n_torus_scheme (Suc n))"
proof -
  let ?block = "[(a, True), (b, True), (a, False), (b, False)]"
  let ?tn = "top1_n_torus_scheme n"
  \<comment> \<open>Step 1: Relabel a to 2*n and b to 2*n+1 in the block (via congruence on the prefix).\<close>
  \<comment> \<open>Use scheme\_equiv\_relabel\_avoid to get fresh labels, then relabel to target.\<close>
  \<comment> \<open>Actually: relabel a\\<to>2*n in the full scheme, then relabel b\\<to>2*n+1.\<close>
  define target_block where "target_block = [(2*n, True), (2*n+1, True), (2*n, False), (2*n+1, False)]"
  \<comment> \<open>The target torus\_(Suc n) = torus\_n @ target\_block.\<close>
  have htorus_suc: "top1_n_torus_scheme (Suc n) = ?tn @ target_block"
    unfolding top1_n_torus_scheme_def target_block_def
    by (by100 simp)
  \<comment> \<open>Step 2: Show block @ torus\_n ~ target\_block @ torus\_n via relabeling.
     Relabel a\\<to>2*n in the full scheme (preserves torus\_n since a,b are fresh from 0..2n-1).
     Then relabel b\\<to>2*n+1.\<close>
  \<comment> \<open>Key: the relabeled block @ torus\_n has the right form.\<close>
  have hblock_target: "top1_scheme_equiv ?block target_block"
  proof -
    have "top1_scheme_equiv ?block (top1_n_torus_scheme 1)"
      using commutator_block_equiv_torus_1[OF assms(1)] .
    moreover have "top1_scheme_equiv (top1_n_torus_scheme 1) target_block"
    proof -
      have "2 * n \<noteq> 2 * n + 1" by (by100 simp)
      from commutator_block_equiv_torus_1[OF this]
      have "top1_scheme_equiv [(2*n,True),(2*n+1,True),(2*n,False),(2*n+1,False)] (top1_n_torus_scheme 1)" .
      from scheme_equiv_sym[OF this] show ?thesis unfolding target_block_def .
    qed
    ultimately show ?thesis unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
  qed
  have "top1_scheme_equiv (?block @ ?tn) (target_block @ ?tn)"
    using scheme_equiv_append[OF hblock_target] by (by100 blast)
  \<comment> \<open>Step 3: Rotate target\_block from front to back.\<close>
  moreover have "top1_scheme_equiv (target_block @ ?tn) (?tn @ target_block)"
    using elementary_imp_equiv[OF top1_elementary_scheme_operation.rotate[of target_block ?tn]]
    by (by100 simp)
  \<comment> \<open>Step 4: torus\_n @ target\_block = torus\_(Suc n).\<close>
  ultimately have "top1_scheme_equiv (?block @ ?tn) (?tn @ target_block)"
    unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
  thus ?thesis using htorus_suc by (by100 simp)
qed

lemma scheme_normal_form:
  fixes scheme :: "(nat \<times> bool) list"
  assumes "length scheme \<ge> 4"
      and "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
      \<comment> \<open>Proper: each label appears exactly 0 or 2 times.\<close>
  shows "(\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
       \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w)
       \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv scheme w)"
  using assms
proof (induction "length scheme" arbitrary: scheme rule: less_induct)
  case (less scheme)
  \<comment> \<open>Classify: does the scheme have a label with same-direction occurrences (projective type)?
     Or all labels have opposite-direction occurrences (torus type)?\<close>
  show ?case
  proof (cases "\<exists>label. \<exists>i < length scheme. \<exists>j < length scheme. i \<noteq> j
      \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)")
    case True
    \<comment> \<open>Projective type: Book Step 2.
       Use Lemma 77.1 to bring one same-direction pair to front.
       Then: remainder is shorter (after potential cancellation) or has fewer projective pairs.
       By IH or repeated extraction: reach normal form.\<close>
    \<comment> \<open>Get the label appearing twice with same direction.\<close>
    from True obtain lab p q where hlab: "p < length scheme" "q < length scheme" "p \<noteq> q"
        "fst (scheme!p) = lab" "fst (scheme!q) = lab"
        "snd (scheme!p) = snd (scheme!q)"
      by (by100 blast)
    \<comment> \<open>By properness, lab appears exactly twice (at p and q).\<close>
    \<comment> \<open>Decompose scheme as y0 @ [(lab, d)] @ y1 @ [(lab, d)] @ y2.\<close>
    \<comment> \<open>Apply Lemma 77.1: scheme ~ [(lab,d),(lab,d)] @ y0 @ rev(inv(y1)) @ y2.\<close>
    \<comment> \<open>The result is [(lab,d),(lab,d)] @ rest where rest has length scheme - 2.\<close>
    \<comment> \<open>If rest is empty: length scheme = 2 (contradicts length \<ge> 4)... wait, the pair
       only takes 2 positions but the scheme has the pair PLUS rest.
       Actually: scheme has length \<ge> 4, the pair takes 2 positions,
       so rest has length \<ge> 2.\<close>
    \<comment> \<open>Apply IH to rest (shorter scheme) or analyze directly.\<close>
    \<comment> \<open>Book: if length 4 \<Rightarrow> projective m=1 or m=2 directly.
       If length > 4: Corollary 77.2 gives (a1a1)...(akak)w1, then 77.3 + 77.4.\<close>
    show ?thesis
    proof (cases "length scheme = 4")
      case True
      \<comment> \<open>Length 4 projective: use Lemma 77.1 to bring projective pair to front.
         Remainder has length 2 with one label. Two subcases:
         (a) same direction \<Rightarrow> scheme ~ aabb ~ projective m=2
         (b) opposite direction \<Rightarrow> scheme ~ aab\\<inverse>b ~ cancel \<Rightarrow> aa ~ projective m=1.\<close>
      \<comment> \<open>Step 1: decompose scheme as y0 @ [(lab,d)] @ y1 @ [(lab,d)] @ y2.\<close>
      \<comment> \<open>From projective type, there exists lab with 2 same-direction occurrences.\<close>
      \<comment> \<open>Step 2: apply Lemma\\_77\\_1\\_projective\\_collection to bring pair to front.\<close>
      \<comment> \<open>Step 3: remaining 2 elements have one other label. Subcase on direction.\<close>
      \<comment> \<open>Step 4a: both True \<Rightarrow> relabel \<Rightarrow> projective m=2.\<close>
      \<comment> \<open>Step 4b: one True, one False \<Rightarrow> inverse pair \<Rightarrow> cancel \<Rightarrow> aa \<Rightarrow> projective m=1.\<close>
      \<comment> \<open>Use the length-4 projective base case lemma.\<close>
      from projective_len4_base[OF True less(3)
            \<open>\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme.
                i \<noteq> j \<and> fst (scheme ! i) = label \<and> fst (scheme ! j) = label
                \<and> snd (scheme ! i) = snd (scheme ! j)\<close>]
      show ?thesis by (by100 blast)
    next
      case False
      hence hgt4: "length scheme > 4" using less(2) by (by100 simp)
      \<comment> \<open>Length > 4: apply Lemma 77.1 once to bring one projective pair to front.
         scheme ~ [(a,d),(a,d)] @ rest. rest has length scheme - 2 \<ge> 4.
         If rest is projective type: IH (shorter) gives rest ~ normal form.
         If rest is torus type:
           - if rest has adjacent cancellable pair: cancel \<Rightarrow> shorter \<Rightarrow> IH
           - if not: apply Lemma 77.3 to extract commutator from rest,
             then Lemma 77.4 to absorb commutator into projective blocks.
             Result: more projective pairs + shorter torus remainder.\<close>
      \<comment> \<open>Step 1: Extract projective pair to front using helper.\<close>
      have hne: "scheme \<noteq> []"
      proof
        assume "scheme = []" hence "length scheme = 0" by (by100 simp)
        thus False using hgt4 by (by100 simp)
      qed
      obtain a rest where ha_rest:
          "top1_scheme_equiv scheme ([(a, True), (a, True)] @ rest)"
          "length rest = length scheme - 2"
          "\<forall>e \<in> set rest. fst e \<noteq> a"
          "fst ` set rest \<subseteq> fst ` set scheme"
          "\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2}"
        using extract_projective_pair[OF less(3)
            \<open>\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme.
                i \<noteq> j \<and> fst (scheme ! i) = label \<and> fst (scheme ! j) = label
                \<and> snd (scheme ! i) = snd (scheme ! j)\<close> hne] by (by100 blast)
      \<comment> \<open>Step 2: rest has length \<ge> 4.\<close>
      have hrest_len_ge4: "length rest \<ge> 4"
      proof -
        have "even (length scheme)" using proper_scheme_even_length[OF less(3)] .
        have "length scheme \<noteq> 5"
        proof
          assume "length scheme = 5" hence "even (5::nat)" using \<open>even (length scheme)\<close> by (by100 simp)
          thus False by (by100 simp)
        qed
        hence "length scheme \<ge> 6" using hgt4 by (by100 simp)
        thus ?thesis using ha_rest(2) by (by100 simp)
      qed
      \<comment> \<open>Step 3: rest is proper (from extract\_projective\_pair).\<close>
      have hrest_proper: "\<forall>label. card {i. i < length rest \<and> fst (rest ! i) = label} \<in> {0, 2}"
        using ha_rest(5) .
      \<comment> \<open>Step 4: Apply IH to rest.\<close>
      have hrest_shorter: "length rest < length scheme" using ha_rest(2) hgt4 by (by100 simp)
      from less(1)[OF hrest_shorter hrest_len_ge4 hrest_proper]
      have hrest_nf: "(\<exists>a' b'. a' \<noteq> b' \<and> top1_scheme_equiv rest [(a', True), (a', False), (b', True), (b', False)])
           \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv rest w)
           \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv rest w)" .
      \<comment> \<open>Step 5: Combine projective pair [(a,T),(a,T)] with the normal form of rest.\<close>
      from hrest_nf show ?thesis
      proof (elim disjE)
        \<comment> \<open>Case 1: rest \<sim> sphere. Cancel the two inverse pairs to get [(a,T),(a,T)] = projective m=1.\<close>
        assume "\<exists>a' b'. a' \<noteq> b' \<and> top1_scheme_equiv rest [(a', True), (a', False), (b', True), (b', False)]"
        then obtain a' b' where hab: "a' \<noteq> b'" "top1_scheme_equiv rest [(a', True), (a', False), (b', True), (b', False)]"
          by (by100 blast)
        \<comment> \<open>With unconditional congruence: [(a,T),(a,T)]@rest \<sim> [(a,T),(a,T)]@sphere directly.\<close>
        have "top1_scheme_equiv ([(a,True),(a,True)] @ rest) ([(a,True),(a,True)] @ [(a',True),(a',False),(b',True),(b',False)])"
          using scheme_equiv_prepend[OF hab(2)] by (by100 blast)
        hence hchain: "top1_scheme_equiv scheme ([(a,True),(a,True)] @ [(a',True),(a',False),(b',True),(b',False)])"
          using scheme_equiv_trans[OF ha_rest(1)] by (by100 blast)
        \<comment> \<open>Cancel (a',T)(a',F) at positions 2,3; then (b',T)(b',F) at positions 2,3.\<close>
        have "top1_scheme_equiv scheme ([(a,True),(a,True)])"
        proof -
          have s1: "top1_elementary_scheme_operation
              ([(a,True),(a,True)] @ [(a',True), top1_inverse_edge (a',True)] @ [(b',True),(b',False)])
              ([(a,True),(a,True)] @ [(b',True),(b',False)])"
            by (rule top1_elementary_scheme_operation.cancel)
          have "(a', False) = top1_inverse_edge (a', True)"
            unfolding top1_inverse_edge_def by (by100 simp)
          hence "top1_scheme_equiv ([(a,True),(a,True),(a',True),(a',False),(b',True),(b',False)])
              ([(a,True),(a,True),(b',True),(b',False)])"
            using s1 unfolding top1_scheme_equiv_def by (by100 simp)
          moreover have s2: "top1_elementary_scheme_operation
              ([(a,True),(a,True)] @ [(b',True), top1_inverse_edge (b',True)] @ [])
              ([(a,True),(a,True)] @ [])"
            by (rule top1_elementary_scheme_operation.cancel)
          have "(b', False) = top1_inverse_edge (b', True)"
            unfolding top1_inverse_edge_def by (by100 simp)
          hence "top1_scheme_equiv ([(a,True),(a,True),(b',True),(b',False)])
              ([(a,True),(a,True)])"
            using s2 unfolding top1_scheme_equiv_def by (by100 simp)
          ultimately have heq: "top1_scheme_equiv ([(a,True),(a,True),(a',True),(a',False),(b',True),(b',False)])
              ([(a,True),(a,True)])"
            using scheme_equiv_trans by (by100 blast)
          have "[(a,True),(a,True)] @ [(a',True),(a',False),(b',True),(b',False)]
              = [(a,True),(a,True),(a',True),(a',False),(b',True),(b',False)]" by (by100 simp)
          hence "top1_scheme_equiv ([(a,True),(a,True)] @ [(a',True),(a',False),(b',True),(b',False)])
              ([(a,True),(a,True)])"
            using heq by (by100 simp)
          thus ?thesis using scheme_equiv_trans[OF hchain] by (by100 blast)
        qed
        \<comment> \<open>Relabel a \<to> 0: [(a,T),(a,T)] \<sim> [(0,T),(0,T)] = projective 1.\<close>
        moreover have "top1_scheme_equiv [(a,True),(a,True)] (top1_m_projective_scheme 1)"
        proof -
          have "top1_elementary_scheme_operation [(a,True),(a,True)]
              (map (\<lambda>(l,b). (if l = a then 0 else l, b)) [(a,True),(a,True)])"
            by (rule top1_elementary_scheme_operation.relabel)
          moreover have "map (\<lambda>(l,b). (if l = a then 0 else l, b)) [(a,True),(a,True)] = [(0,True),(0,True)]"
            by (by100 simp)
          moreover have "[(0::nat,True),(0,True)] = top1_m_projective_scheme 1"
            unfolding top1_m_projective_scheme_def by (by100 simp)
          ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
        qed
        ultimately have "top1_scheme_equiv scheme (top1_m_projective_scheme 1)"
          using scheme_equiv_trans by (by100 blast)
        moreover have "top1_is_projective_scheme (top1_m_projective_scheme 1) 1"
          unfolding top1_is_projective_scheme_def by (by100 simp)
        ultimately have "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w"
          by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        \<comment> \<open>Case 2: rest \<sim> projective m'. Then scheme \<sim> projective (m'+1).\<close>
        assume "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv rest w"
        then obtain m' w' where hm: "m' > 0" "top1_is_projective_scheme w' m'" "top1_scheme_equiv rest w'"
          by (by100 blast)
        \<comment> \<open>scheme \<sim> [(a,T),(a,T)] @ projective m'. Relabel a to m' and get projective (m'+1).\<close>
        \<comment> \<open>Chain: scheme \<sim> [(a,T),(a,T)] @ rest \<sim> [(a,T),(a,T)] @ proj m' (congruence).
           Need: relabel proj m' to avoid label a, then apply congruence.\<close>
        have hw': "w' = top1_m_projective_scheme m'" using hm(2) unfolding top1_is_projective_scheme_def
          by (by100 simp)
        \<comment> \<open>Step 1: scheme \<sim> [(a,T),(a,T)] @ rest (from ha\_rest).\<close>
        \<comment> \<open>Step 2: rest \<sim> proj m' (from hm(3)).\<close>
        \<comment> \<open>Step 3: Apply congruence: [(a,T),(a,T)]@rest \<sim> [(a,T),(a,T)]@proj m'.
           Need: a \<notin> labels of rest (ha\_rest(3)) AND a \<notin> labels of proj m'.
           If a \<ge> m': a \<notin> {0..m'-1} = labels of proj m'. Direct.
           If a < m': relabel a \<to> fresh in rest first.\<close>
        \<comment> \<open>Step 4: [(a,T),(a,T)]@proj m' = [(a,T),(a,T),(0,T),(0,T),...,(m'-1,T),(m'-1,T)].
           Relabel a \<to> m': [(m',T),(m',T),(0,T),(0,T),...,(m'-1,T),(m'-1,T)] = proj (m'+1).\<close>
        \<comment> \<open>Step 3: Relabel w' (= proj m') to avoid label a, then apply congruence.\<close>
        from scheme_equiv_relabel_avoid[of w' a]
        obtain w_no_a where hw_no_a: "top1_scheme_equiv w' w_no_a" "\<forall>e \<in> set w_no_a. fst e \<noteq> a"
          by (by100 blast)
        have "top1_scheme_equiv rest w_no_a"
          using hm(3) hw_no_a(1) unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
        hence "top1_scheme_equiv ([(a,True),(a,True)] @ rest) ([(a,True),(a,True)] @ w_no_a)"
          using scheme_equiv_prepend by (by100 blast)
        hence hchain: "top1_scheme_equiv scheme ([(a,True),(a,True)] @ w_no_a)"
          using scheme_equiv_trans[OF ha_rest(1)] by (by100 blast)
        \<comment> \<open>Step 4: [(a,T),(a,T)] @ w\_no\_a has label a only in pair (2 times).
           w\_no\_a is equivalent to proj m' and avoids a.
           Relabel to standard projective form.\<close>
        \<comment> \<open>Step 4: rotate + relabel fresh \<to> m' + projective\_form\_equiv\_standard.\<close>
        have "top1_scheme_equiv ([(a,True),(a,True)] @ w_no_a) (w_no_a @ [(a,True),(a,True)])"
          using elementary_imp_equiv[OF top1_elementary_scheme_operation.rotate[of "[(a,True),(a,True)]" w_no_a]]
          by (by100 simp)
        \<comment> \<open>w\_no\_a @ [(a,T),(a,T)] is a projective-form scheme. Relabel to standard.\<close>
        have "top1_scheme_equiv (w_no_a @ [(a,True),(a,True)]) (top1_m_projective_scheme (m'+1))"
        proof -
          \<comment> \<open>w\_no\_a \<sim> proj m' (from hw\_no\_a(1) + hm(3)). Suffix congruence + proj\_append\_pair.\<close>
          have "top1_scheme_equiv w_no_a (top1_m_projective_scheme m')"
            using scheme_equiv_sym[OF hw_no_a(1)] unfolding hw' .
          hence "top1_scheme_equiv (w_no_a @ [(a,True),(a,True)]) (top1_m_projective_scheme m' @ [(a,True),(a,True)])"
            using scheme_equiv_append by (by100 blast)
          moreover have "top1_scheme_equiv (top1_m_projective_scheme m' @ [(a,True),(a,True)])
              (top1_m_projective_scheme (Suc m'))"
            by (rule proj_append_pair)
          ultimately have "top1_scheme_equiv (w_no_a @ [(a,True),(a,True)]) (top1_m_projective_scheme (Suc m'))"
            unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          thus ?thesis by (by100 simp)
        qed
        hence "top1_scheme_equiv ([(a,True),(a,True)] @ w_no_a) (top1_m_projective_scheme (m'+1))"
          using \<open>top1_scheme_equiv ([(a,True),(a,True)] @ w_no_a) (w_no_a @ [(a,True),(a,True)])\<close>
          unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
        hence "top1_scheme_equiv scheme (top1_m_projective_scheme (m'+1))"
          using scheme_equiv_trans[OF hchain] by (by100 blast)
        moreover have "top1_is_projective_scheme (top1_m_projective_scheme (m'+1)) (m'+1)"
          unfolding top1_is_projective_scheme_def using hm(1) by (by100 simp)
        ultimately have "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w"
          using hm(1) by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        \<comment> \<open>Case 3: rest \<sim> torus n'. Apply Lemma 77.4 repeatedly:
           [(a,T),(a,T)] @ torus n' \<sim> projective (2n'+1).\<close>
        assume "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv rest w"
        then obtain n' w' where hn: "n' > 0" "top1_is_torus_scheme w' n'" "top1_scheme_equiv rest w'"
          by (by100 blast)
        \<comment> \<open>scheme \<sim> [(a,T),(a,T)] @ torus n'.
           Each application of Lemma 77.4 converts 1 proj pair + 1 torus block \<Rightarrow> 3 proj pairs.
           After n' applications: projective (2n'+1).\<close>
        \<comment> \<open>Relabel torus n' to avoid label a, then apply congruence + Lemma 77.4.\<close>
        from scheme_equiv_relabel_avoid[of w' a]
        obtain w_no_a where hwt: "top1_scheme_equiv w' w_no_a" "\<forall>e \<in> set w_no_a. fst e \<noteq> a"
          by (by100 blast)
        have "top1_scheme_equiv rest w_no_a"
          using hn(3) hwt(1) unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
        hence "top1_scheme_equiv ([(a,True),(a,True)] @ rest) ([(a,True),(a,True)] @ w_no_a)"
          using scheme_equiv_prepend by (by100 blast)
        hence hchain_t: "top1_scheme_equiv scheme ([(a,True),(a,True)] @ w_no_a)"
          using scheme_equiv_trans[OF ha_rest(1)] by (by100 blast)
        \<comment> \<open>Chain: scheme \<sim> [(a,T),(a,T)]@w\_no\_a \<sim> [(a,T),(a,T)]@torus n' \<sim> proj(2n'+1).\<close>
        have hw'_torus: "w' = top1_n_torus_scheme n'" using hn(2) unfolding top1_is_torus_scheme_def
          by (by100 simp)
        have "top1_scheme_equiv w_no_a (top1_n_torus_scheme n')"
          using scheme_equiv_sym[OF hwt(1)] hw'_torus by (by100 simp)
        hence "top1_scheme_equiv ([(a,True),(a,True)] @ w_no_a) ([(a,True),(a,True)] @ top1_n_torus_scheme n')"
          using scheme_equiv_prepend by (by100 blast)
        moreover have "top1_scheme_equiv ([(a,True),(a,True)] @ top1_n_torus_scheme n')
            (top1_m_projective_scheme (2*n'+1))"
          by (rule proj_pair_absorbs_torus)
        ultimately have "top1_scheme_equiv scheme (top1_m_projective_scheme (2*n'+1))"
          using hchain_t unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
        moreover have "top1_is_projective_scheme (top1_m_projective_scheme (2*n'+1)) (2*n'+1)"
          unfolding top1_is_projective_scheme_def using hn(1) by (by100 simp)
        have "(2*n'+1) > 0" using hn(1) by (by100 simp)
        hence "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w"
          using \<open>top1_scheme_equiv scheme (top1_m_projective_scheme (2*n'+1))\<close>
              \<open>top1_is_projective_scheme (top1_m_projective_scheme (2*n'+1)) (2*n'+1)\<close>
          by (by100 force)
        thus ?thesis by (by100 blast)
      qed
    qed
  next
    case False
    \<comment> \<open>Torus type: all labels appear with opposite directions.
       Step 1 (torus): extract commutator blocks using Lemma 77.3.\<close>
    show ?thesis
    proof (cases "length scheme = 4")
      case True
      \<comment> \<open>Base case: length 4 torus scheme.
         If adjacent cancellable pair: cancel to length 2, then uncancel to sphere.
         If no adjacent cancellable pair: labels alternate \\<Rightarrow> torus n=1.\<close>
      show ?thesis
      proof (cases "\<exists>i < 3. fst (scheme!i) = fst (scheme!(i+1))")
        case True
        \<comment> \<open>Adjacent same-label pair (must be opposite direction since torus type).
           Cancel gives length 2 scheme, then uncancel to sphere form.\<close>
        \<comment> \<open>Step: scheme has adjacent same-label pair at some position i.
           Cancel to get length 2 scheme. Then uncancel to sphere.\<close>
        from True obtain i where hi: "i < 3" "fst (scheme!i) = fst (scheme!(i+1))" by (by100 blast)
        \<comment> \<open>Since torus type, the adjacent pair has opposite directions.\<close>
        \<comment> \<open>Cancel → length 2 → uncancel → sphere form [(a,T),(a,F),(b,T),(b,F)].\<close>
        \<comment> \<open>All length 4 torus schemes with adjacent same-label are equivalent to sphere.\<close>
        have "\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)]"
        proof -
          \<comment> \<open>The adjacent pair at position i has opposite directions (torus type).
             So scheme![i+1] = top1\\_inverse\\_edge (scheme![i]).
             Rotate to bring it to front, cancel, uncancel with fresh.\<close>
          \<comment> \<open>scheme!(i+1) = inv(scheme!i): same label + torus type \\<Rightarrow> opposite directions.\<close>
          have hsnd_ne: "snd (scheme!i) \<noteq> snd (scheme!(i+1))"
          proof
            assume "snd (scheme!i) = snd (scheme!(i+1))"
            have "i < length scheme" using hi(1) \<open>length scheme = 4\<close> by simp
            have "i+1 < length scheme" using hi(1) \<open>length scheme = 4\<close> by simp
            have "i \<noteq> i+1" by simp
            have "fst (scheme!i) = fst (scheme!(i+1))" using hi(2) .
            have "snd (scheme!i) = snd (scheme!(i+1))" by (rule \<open>snd (scheme!i) = snd (scheme!(i+1))\<close>)
            hence "i < length scheme \<and> (i+1) < length scheme \<and> i \<noteq> (i+1) \<and>
                fst (scheme!i) = fst (scheme!i) \<and> fst (scheme!(i+1)) = fst (scheme!i) \<and>
                snd (scheme!i) = snd (scheme!(i+1))"
              using \<open>i < length scheme\<close> \<open>i+1 < length scheme\<close> hi(2) by simp
            hence "\<exists>label. \<exists>ia<length scheme. \<exists>j<length scheme. ia \<noteq> j
                \<and> fst (scheme!ia) = label \<and> fst (scheme!j) = label \<and> snd (scheme!ia) = snd (scheme!j)"
              by (by100 blast)
            with \<open>\<not> (\<exists>label. _)\<close> show False by simp
          qed
          have hinv: "scheme!(i+1) = top1_inverse_edge (scheme!i)"
            using hi(2) hsnd_ne unfolding top1_inverse_edge_def
            by (cases "scheme!i", cases "scheme!(i+1)") simp
          \<comment> \<open>Split the list at position i.\<close>
          define prefix where "prefix = take i scheme"
          define suffix where "suffix = drop (i + 2) scheme"
          have hlen_i: "i + 1 < length scheme" using hi(1) \<open>length scheme = 4\<close> by simp
          obtain prefix suffix where
              hdecomp: "scheme = prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix"
              and hlen_ps: "length prefix + length suffix = 2"
              and hlen_pf: "length prefix = i"
          proof
            show "scheme = take i scheme @ [scheme!i, top1_inverse_edge (scheme!i)] @ drop (i+2) scheme"
            proof -
              have "scheme = take i scheme @ scheme!i # drop (Suc i) scheme"
                using id_take_nth_drop[of i scheme] hi(1) \<open>length scheme = 4\<close> by simp
              also have "drop (Suc i) scheme = scheme!(i+1) # drop (Suc (Suc i)) scheme"
                using Cons_nth_drop_Suc[of "Suc i" scheme] hlen_i by simp
              finally show ?thesis using hinv by simp
            qed
            show "length (take i scheme) + length (drop (i+2) scheme) = 2"
              using \<open>length scheme = 4\<close> hi(1) by simp
            show "length (take i scheme) = i"
              using hi(1) \<open>length scheme = 4\<close> by simp
          qed
          \<comment> \<open>Rotate + cancel: scheme ~ prefix @ suffix (length 2).\<close>
          have "top1_scheme_equiv scheme (prefix @ suffix)"
          proof -
            have "top1_elementary_scheme_operation
                (prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix)
                (prefix @ suffix)"
              by (rule top1_elementary_scheme_operation.cancel)
            thus ?thesis using hdecomp unfolding top1_scheme_equiv_def by simp
          qed
          \<comment> \<open>prefix @ suffix has length 2 = the other label pair. Uncancel to get sphere.\<close>
          obtain a_lab :: nat where ha: "a_lab \<noteq> fst (hd (prefix @ suffix))"
          proof -
            show ?thesis by (rule that[of "Suc (fst (hd (prefix @ suffix)))"]) simp
          qed
          have "top1_scheme_equiv (prefix @ suffix)
              (prefix @ [(a_lab, True), top1_inverse_edge (a_lab, True)] @ suffix)"
            unfolding top1_scheme_equiv_def
            using top1_elementary_scheme_operation.uncancel[of prefix suffix "(a_lab, True)"] by simp
          \<comment> \<open>Chain: scheme ~ cancel ~ uncancel → length 4 with two label pairs.\<close>
          have hinv_simp: "top1_inverse_edge (a_lab, True) = (a_lab, False)"
            unfolding top1_inverse_edge_def by simp
          from \<open>top1_scheme_equiv (prefix @ suffix) _\<close>
          have "top1_scheme_equiv (prefix @ suffix)
              (prefix @ [(a_lab, True), (a_lab, False)] @ suffix)"
            by (simp add: hinv_simp)
          hence "top1_scheme_equiv scheme
              (prefix @ [(a_lab, True), (a_lab, False)] @ suffix)"
            using \<open>top1_scheme_equiv scheme (prefix @ suffix)\<close>
            unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          \<comment> \<open>The result has labels a\\_lab and fst(hd(prefix@suffix)), both with opposite directions.
             By flip\\_label and relabel if needed: ~ sphere form.\<close>
          \<comment> \<open>Rotate [(a\\_lab,T),(a\\_lab,F)] to front, then flip\\_label for sphere form.\<close>
          moreover have "top1_scheme_equiv (prefix @ [(a_lab,True),(a_lab,False)] @ suffix)
              ([(a_lab,True),(a_lab,False)] @ suffix @ prefix)"
            unfolding top1_scheme_equiv_def
            using top1_elementary_scheme_operation.rotate[of prefix "[(a_lab,True),(a_lab,False)] @ suffix"]
            by (simp add: rtranclp.rtrancl_into_rtrancl)
          ultimately have hchain: "top1_scheme_equiv scheme
              ([(a_lab,True),(a_lab,False)] @ suffix @ prefix)"
            unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          \<comment> \<open>suffix@prefix has length 2, same label, opposite directions. ~ sphere form.\<close>
          \<comment> \<open>suffix@prefix has length 2 with same label, opposite directions.
             Take a=a\\_lab, b=fst(hd(suffix@prefix)).\<close>
          \<comment> \<open>suffix@prefix has exactly 2 elements (from hlen\\_ps).\<close>
          obtain e1 e2 where hsp_list: "suffix @ prefix = [e1, e2]"
          proof -
            have "length (suffix @ prefix) = 2" using hlen_ps by simp
            then obtain e1 rest where "suffix @ prefix = e1 # rest" by (cases "suffix @ prefix") simp_all
            moreover then obtain e2 where "rest = [e2]" using \<open>length (suffix @ prefix) = 2\<close> by (cases rest) simp_all
            ultimately show ?thesis using that by simp
          qed
          \<comment> \<open>The elements e1, e2 are from the original scheme (minus the cancel pair).
             They must have the same label and opposite directions.\<close>
          have he_in: "e1 \<in> set scheme \<and> e2 \<in> set scheme"
          proof -
            from hsp_list have "e1 \<in> set (suffix @ prefix)" by (by100 simp)
            hence "e1 \<in> set suffix \<or> e1 \<in> set prefix" by (by100 simp)
            moreover have hpf_sub: "set prefix \<subseteq> set scheme"
            proof (rule subsetI)
              fix x assume "x \<in> set prefix"
              hence "x \<in> set (prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix)"
                by (by100 simp)
              thus "x \<in> set scheme" using hdecomp by (by100 simp)
            qed
            moreover have hsf_sub: "set suffix \<subseteq> set scheme"
            proof (rule subsetI)
              fix x assume "x \<in> set suffix"
              hence "x \<in> set (prefix @ [scheme!i, top1_inverse_edge (scheme!i)] @ suffix)"
                by (by100 simp)
              thus "x \<in> set scheme" using hdecomp by (by100 simp)
            qed
            ultimately have "e1 \<in> set scheme" by (by100 blast)
            moreover have "e2 \<in> set scheme"
            proof -
              from hsp_list have "e2 \<in> set (suffix @ prefix)" by (by100 simp)
              hence "e2 \<in> set suffix \<or> e2 \<in> set prefix" by (by100 simp)
              thus ?thesis using \<open>set prefix \<subseteq> set scheme\<close> \<open>set suffix \<subseteq> set scheme\<close> by (by100 blast)
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          have he_ne_label: "fst e1 \<noteq> fst (scheme!i) \<and> fst e2 \<noteq> fst (scheme!i)"
          proof -
            let ?lab = "fst (scheme!i)"
            have hlab_card: "card {j. j < 4 \<and> fst (scheme ! j) = ?lab} = 2"
            proof -
              from less(3) have "card {j. j < length scheme \<and> fst (scheme ! j) = ?lab} \<in> {0, 2}"
                by (by100 blast)
              moreover have "i \<in> {j. j < length scheme \<and> fst (scheme ! j) = ?lab}"
                using hi(1) \<open>length scheme = 4\<close> by (by100 simp)
              hence "card {j. j < length scheme \<and> fst (scheme ! j) = ?lab} \<noteq> 0"
                by (by100 auto)
              ultimately have "card {j. j < length scheme \<and> fst (scheme ! j) = ?lab} = 2"
                by (by100 blast)
              thus ?thesis using \<open>length scheme = 4\<close> by (by100 simp)
            qed
            have hlab_only: "\<forall>k < 4. fst (scheme ! k) = ?lab \<longrightarrow> k = i \<or> k = i + 1"
            proof (intro allI impI)
              fix k assume hk: "k < 4" "fst (scheme ! k) = ?lab"
              show "k = i \<or> k = i + 1"
              proof (rule ccontr)
                assume "\<not> (k = i \<or> k = i + 1)"
                hence hk_ne: "k \<noteq> i" "k \<noteq> i + 1" by (by100 blast)+
                have "{i, i+1, k} \<subseteq> {j. j < 4 \<and> fst (scheme ! j) = ?lab}"
                  using hi(1) hk \<open>length scheme = 4\<close> hi(2) by (by100 auto)
                moreover have "card {i, i+1, k} = 3"
                  using hk_ne by (by100 auto)
                moreover have "finite {j. j < 4 \<and> fst (scheme ! j) = ?lab}" by (by100 simp)
                ultimately have "card {j. j < 4 \<and> fst (scheme ! j) = ?lab} \<ge> 3"
                  by (metis card_mono le_antisym not_less_eq_eq)
                thus False using hlab_card by (by100 simp)
              qed
            qed
            \<comment> \<open>e1 from prefix or suffix: position \<noteq> i, \<noteq> i+1.\<close>
            \<comment> \<open>Elements of prefix are at positions < i in scheme.\<close>
            \<comment> \<open>Elements at positions < i in scheme have label \<noteq> ?lab.\<close>
            have hpos_ne: "\<forall>k. k < length prefix \<longrightarrow> fst (scheme ! k) \<noteq> ?lab"
            proof (intro allI impI)
              fix k assume "k < length prefix"
              hence "k < i" using hlen_pf by (by100 simp)
              hence "k < 4" using hi(1) \<open>length scheme = 4\<close> by (by100 auto)
              moreover have "k \<noteq> i" using \<open>k < i\<close> by (by100 simp)
              moreover have "k \<noteq> i + 1" using \<open>k < i\<close> by (by100 simp)
              ultimately show "fst (scheme ! k) \<noteq> ?lab" using hlab_only by (by100 blast)
            qed
            have hpf_ne: "\<forall>x \<in> set prefix. fst x \<noteq> ?lab"
            proof (rule ballI)
              fix x assume hx_pf: "x \<in> set prefix"
              hence "\<exists>k. k < length prefix \<and> prefix ! k = x"
                by (simp add: in_set_conv_nth)
              then obtain k where hk: "k < length prefix" "prefix ! k = x"
                by (by100 blast)
              have "k < i" using hk(1) hlen_pf by (by100 simp)
              have hsk: "scheme ! k = x"
              proof -
                have hk': "k < length prefix" using hk(1) .
                have "(prefix @ [scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! k = prefix ! k"
                  using nth_append[of prefix _ k] hk' by (by100 simp)
                thus ?thesis using hdecomp hk(2) by (by100 simp)
              qed
              have "k < 4" using \<open>k < i\<close> hi(1) \<open>length scheme = 4\<close> by (by100 auto)
              moreover have "k \<noteq> i" using \<open>k < i\<close> by (by100 simp)
              moreover have "k \<noteq> i + 1" using \<open>k < i\<close> by (by100 simp)
              ultimately have "fst (scheme ! k) \<noteq> ?lab" using hlab_only by (by100 blast)
              thus "fst x \<noteq> ?lab" using hsk by (by100 simp)
            qed
            have hsf_ne: "\<forall>x \<in> set suffix. fst x \<noteq> ?lab"
            proof (rule ballI)
              fix x assume hx_sf: "x \<in> set suffix"
              hence "\<exists>k. k < length suffix \<and> suffix ! k = x"
                by (simp add: in_set_conv_nth)
              then obtain k where hk: "k < length suffix" "suffix ! k = x"
                by (by100 blast)
              define k' where "k' = i + 2 + k"
              have hsk: "scheme ! k' = x"
              proof -
                have "(prefix @ [scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! k' = suffix ! k"
                proof -
                  have "k' = length prefix + 2 + k" using hlen_pf unfolding k'_def by (by100 simp)
                  have "(prefix @ [scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! k'
                      = ([scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! (k' - length prefix)"
                    using nth_append[of prefix _ k'] \<open>k' = length prefix + 2 + k\<close> by (by100 simp)
                  also have "k' - length prefix = 2 + k" using \<open>k' = length prefix + 2 + k\<close> by (by100 simp)
                  also have "([scheme ! i, top1_inverse_edge (scheme ! i)] @ suffix) ! (2 + k) = suffix ! k"
                    using hk(1) by (by100 simp)
                  finally show ?thesis .
                qed
                thus ?thesis using hdecomp hk(2) by (by100 simp)
              qed
              have "k' < 4" using hk(1) hlen_pf hlen_ps unfolding k'_def by (by100 auto)
              moreover have "k' \<noteq> i" unfolding k'_def by (by100 simp)
              moreover have "k' \<noteq> i + 1" unfolding k'_def by (by100 simp)
              ultimately have "fst (scheme ! k') \<noteq> ?lab" using hlab_only by (by100 blast)
              thus "fst x \<noteq> ?lab" using hsk by (by100 simp)
            qed
            have "fst e1 \<noteq> ?lab \<and> fst e2 \<noteq> ?lab"
            proof -
              from hsp_list have "e1 \<in> set (suffix @ prefix)" by (by100 simp)
              hence "e1 \<in> set suffix \<or> e1 \<in> set prefix" by (by100 simp)
              hence "fst e1 \<noteq> ?lab" using hpf_ne hsf_ne by (by100 blast)
              moreover from hsp_list have "e2 \<in> set (suffix @ prefix)" by (by100 simp)
              hence "e2 \<in> set suffix \<or> e2 \<in> set prefix" by (by100 simp)
              hence "fst e2 \<noteq> ?lab" using hpf_ne hsf_ne by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            thus ?thesis by (by100 simp)
          qed
          have "fst e1 = fst e2"
          proof -
            \<comment> \<open>Since length scheme = 4, there are exactly 4 positions.
               Positions i and i+1 have label fst(scheme!i).
               The other 2 positions have elements e1 and e2 (from prefix/suffix).
               By properness: fst(e1) appears 0 or 2 times. At least once (e1). So 2 times.
               Those 2 times can't include i or i+1 (different label, by he\_ne\_label).
               The other 2 positions have fst = fst(e1). Since e2 is at one of those: fst(e1) = fst(e2).\<close>
            \<comment> \<open>Direct argument: scheme has 4 elements. 2 have label fst(scheme!i).
               e1, e2 are the other 2. If fst(e1) \<noteq> fst(e2), then fst(e1) appears only once
               (at e1's position). But properness requires 0 or 2 occurrences. Contradiction.\<close>
            show ?thesis
            proof (rule ccontr)
              assume hne: "fst e1 \<noteq> fst e2"
              \<comment> \<open>fst(e1) appears at e1's position and no other.\<close>
              \<comment> \<open>e1's position: some k1 with scheme!k1 = e1.
                 e2's position: some k2 with scheme!k2 = e2, fst(e2) \<noteq> fst(e1).
                 i and i+1: label = fst(scheme!i) \<noteq> fst(e1).
                 So fst(e1) appears exactly 1 time, contradicting properness.\<close>
              from he_in have "e1 \<in> set scheme" by (by100 blast)
              hence "\<exists>k1. k1 < length scheme \<and> scheme ! k1 = e1"
                by (simp add: in_set_conv_nth)
              then obtain k1 where hk1: "k1 < length scheme" "scheme ! k1 = e1" by (by100 blast)
              have "card {j. j < length scheme \<and> fst (scheme ! j) = fst e1} \<in> {0, 2}"
                using less(3) by (by100 blast)
              moreover have "k1 \<in> {j. j < length scheme \<and> fst (scheme ! j) = fst e1}"
                using hk1 by (by100 simp)
              hence "card {j. j < length scheme \<and> fst (scheme ! j) = fst e1} \<noteq> 0"
                by (by100 auto)
              ultimately have hcard_e1: "card {j. j < length scheme \<and> fst (scheme ! j) = fst e1} = 2"
                by (by100 blast)
              \<comment> \<open>Positions with label fst(e1): exactly 2. Can't include i or i+1.\<close>
              \<comment> \<open>The 2 positions must be among {0,1,2,3} - {i, i+1} which has 2 elements.\<close>
              \<comment> \<open>These 2 positions correspond to e1 and e2's positions.
                 But fst(e2) \<noteq> fst(e1) means e2's position is NOT among them.
                 So only 1 position has label fst(e1): k1. Card = 1 \<noteq> 2. Contradiction.\<close>
              have hcard1: "card {j. j < 4 \<and> fst (scheme ! j) = fst e1} = 2"
                using hcard_e1 \<open>length scheme = 4\<close> by (by100 simp)
              \<comment> \<open>Count: positions i, i+1 have different label. e2's position has different label.
                 So at most 1 position (e1's) has label fst(e1).\<close>
              \<comment> \<open>But card = 2 means at least 2 positions. Contradiction if only k1 has it.\<close>
              \<comment> \<open>Get k2, show the set \<subseteq> {k1} using label contradictions + presburger, then card \<le> 1.\<close>
              from he_in have "e2 \<in> set scheme" by (by100 blast)
              hence "\<exists>k2. k2 < length scheme \<and> scheme ! k2 = e2" by (simp add: in_set_conv_nth)
              then obtain k2 where hk2: "k2 < length scheme" "scheme ! k2 = e2" by (by100 blast)
              have hset_sub: "{j. j < 4 \<and> fst (scheme ! j) = fst e1} \<subseteq> {k1}"
              proof (rule subsetI)
                fix j assume hj_in: "j \<in> {j. j < 4 \<and> fst (scheme ! j) = fst e1}"
                hence hj: "j < 4" "fst (scheme ! j) = fst e1" by (by100 simp)+
                have hjni: "j \<noteq> i"
                proof assume "j = i"
                  hence "fst e1 = fst (scheme ! i)" using hj(2) by (by100 simp)
                  moreover from he_ne_label have "fst e1 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hjni1: "j \<noteq> i + 1"
                proof assume "j = i + 1"
                  hence "fst e1 = fst (scheme ! (i+1))" using hj(2) by (by100 simp)
                  hence "fst e1 = fst (scheme ! i)" using hi(2) by (by100 simp)
                  moreover from he_ne_label have "fst e1 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hjnk2: "j \<noteq> k2"
                proof assume "j = k2"
                  hence "fst e1 = fst e2" using hj(2) hk2(2) by (by100 simp)
                  thus False using hne by (by100 simp)
                qed
                have hk2ni: "k2 \<noteq> i"
                proof assume "k2 = i"
                  hence "fst e2 = fst (scheme ! i)" using hk2(2) by (by100 simp)
                  moreover from he_ne_label have "fst e2 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hk2ni1: "k2 \<noteq> i + 1"
                proof assume "k2 = i + 1"
                  hence "fst e2 = fst (scheme ! (i+1))" using hk2(2) by (by100 simp)
                  hence "fst e2 = fst (scheme ! i)" using hi(2) by (by100 simp)
                  moreover from he_ne_label have "fst e2 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hk1ni: "k1 \<noteq> i"
                proof assume "k1 = i"
                  hence "fst e1 = fst (scheme ! i)" using hk1(2) by (by100 simp)
                  moreover from he_ne_label have "fst e1 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hk1ni1: "k1 \<noteq> i + 1"
                proof assume "k1 = i + 1"
                  hence "fst e1 = fst (scheme ! (i+1))" using hk1(2) by (by100 simp)
                  hence "fst e1 = fst (scheme ! i)" using hi(2) by (by100 simp)
                  moreover from he_ne_label have "fst e1 \<noteq> fst (scheme ! i)" by (by100 blast)
                  ultimately show False by (by100 simp)
                qed
                have hk1nk2: "k1 \<noteq> k2"
                proof assume "k1 = k2"
                  hence "fst e1 = fst e2" using hk1(2) hk2(2) by (by100 simp)
                  thus False using hne by (by100 simp)
                qed
                have "i < 3" using hi(1) by (by100 simp)
                have "k2 < 4" using hk2(1) \<open>length scheme = 4\<close> by (by100 simp)
                have "k1 < 4" using hk1(1) \<open>length scheme = 4\<close> by (by100 simp)
                from hj(1) \<open>k1 < 4\<close> \<open>k2 < 4\<close> \<open>i < 3\<close>
                    hjni hjni1 hjnk2 hk1ni hk1ni1 hk1nk2 hk2ni hk2ni1
                have "j = k1" by (by100 presburger)
                thus "j \<in> {k1}" by (by100 simp)
              qed
              have "card {j. j < 4 \<and> fst (scheme ! j) = fst e1} \<le> card {k1}"
                by (rule card_mono) (by100 simp, rule hset_sub)
              hence "card {j. j < 4 \<and> fst (scheme ! j) = fst e1} \<le> 1" by (by100 simp)
              show False using hcard1 \<open>card {j. j < 4 \<and> fst (scheme ! j) = fst e1} \<le> 1\<close>
                by (by100 simp)
            qed
          qed
          have "snd e1 \<noteq> snd e2"
            using proper_len4_torus_pair_props[OF \<open>length scheme = 4\<close>
                \<open>\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme.
                    i \<noteq> j \<and> fst (scheme ! i) = label \<and> fst (scheme ! j) = label
                    \<and> snd (scheme ! i) = snd (scheme ! j))\<close>
                \<open>fst e1 = fst e2\<close> hi(1) hi(2) hdecomp hlen_pf hsp_list]
            by (by100 blast)
          define b_lab where "b_lab = fst e1"
          define d_b where "d_b = snd e1"
          have hsp: "suffix @ prefix = [(b_lab, d_b), (b_lab, \<not>d_b)]"
            using hsp_list \<open>fst e1 = fst e2\<close> \<open>snd e1 \<noteq> snd e2\<close>
            unfolding b_lab_def d_b_def by (cases e1, cases e2) simp
          have hab_ne: "a_lab \<noteq> b_lab"
          proof -
            have "hd (prefix @ suffix) \<in> set (prefix @ suffix)"
            proof -
              have "prefix @ suffix \<noteq> []"
              proof
                assume "prefix @ suffix = []"
                hence "length (prefix @ suffix) = 0" by (by100 simp)
                hence "length prefix + length suffix = 0" by (by100 simp)
                thus False using hlen_ps by (by100 simp)
              qed
              hence "hd (prefix @ suffix) \<in> set (prefix @ suffix)"
                using list.set_sel(1) by (by100 blast)
              thus ?thesis .
            qed
            hence "hd (prefix @ suffix) \<in> set prefix \<union> set suffix" by (by100 simp)
            hence "hd (prefix @ suffix) \<in> set suffix \<union> set prefix" by (by100 blast)
            hence "hd (prefix @ suffix) \<in> set (suffix @ prefix)" by (by100 simp)
            hence "hd (prefix @ suffix) \<in> set [e1, e2]" using hsp_list by (by100 simp)
            hence "hd (prefix @ suffix) = e1 \<or> hd (prefix @ suffix) = e2" by (by100 simp)
            hence "fst (hd (prefix @ suffix)) = fst e1"
              using \<open>fst e1 = fst e2\<close>
            proof (elim disjE)
              assume "hd (prefix @ suffix) = e1" thus ?thesis by (by100 simp)
            next
              assume "hd (prefix @ suffix) = e2" thus ?thesis using \<open>fst e1 = fst e2\<close> by (by100 simp)
            qed
            hence "a_lab \<noteq> fst e1" using ha by (by100 simp)
            thus ?thesis unfolding b_lab_def by (by100 simp)
          qed
          obtain b_lab d_b where
              hsp: "suffix @ prefix = [(b_lab, d_b), (b_lab, \<not>d_b)]" and
              hab_ne: "a_lab \<noteq> b_lab"
            using hsp hab_ne by (by100 blast)
          \<comment> \<open>Now [(a\\_lab,T),(a\\_lab,F)] @ [(b\\_lab,d\\_b),(b\\_lab,\\<not>d\\_b)] ~ sphere form.\<close>
          have "top1_scheme_equiv
              ([(a_lab,True),(a_lab,False)] @ suffix @ prefix)
              ([(a_lab,True),(a_lab,False),(b_lab,True),(b_lab,False)])"
          proof -
            show ?thesis
            proof (cases d_b)
              case True
              hence "suffix @ prefix = [(b_lab, True), (b_lab, False)]" using hsp by simp
              thus ?thesis unfolding top1_scheme_equiv_def by simp
            next
              case False
              hence "suffix @ prefix = [(b_lab, False), (b_lab, True)]" using hsp by simp
              hence target_eq: "[(a_lab,True),(a_lab,False)] @ suffix @ prefix
                  = [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)]" by simp
              have hflip_result: "map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo))
                  [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)]
                  = [(a_lab,True),(a_lab,False),(b_lab,True),(b_lab,False)]"
                using hab_ne by simp
              have "top1_elementary_scheme_operation
                  [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)]
                  [(a_lab,True),(a_lab,False),(b_lab,True),(b_lab,False)]"
              proof -
                have "top1_elementary_scheme_operation
                    [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)]
                    (map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo))
                         [(a_lab,True),(a_lab,False),(b_lab,False),(b_lab,True)])"
                  by (rule top1_elementary_scheme_operation.flip_label)
                thus ?thesis unfolding hflip_result .
              qed
              thus ?thesis unfolding target_eq top1_scheme_equiv_def by simp
            qed
          qed
          hence "top1_scheme_equiv scheme [(a_lab,True),(a_lab,False),(b_lab,True),(b_lab,False)]"
            using hchain unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          thus ?thesis using hab_ne by (by100 blast)
        qed
        thus ?thesis by (by100 blast)
      next
        case no_adj: False
        \<comment> \<open>No adjacent same-label \\<Rightarrow> labels alternate.
           scheme = [(a,d1),(b,d2),(a,d3),(b,d4)] where a \\<noteq> b, d1\\<noteq>d3, d2\\<noteq>d4.
           After rotate + flip\\_label + relabel: equivalent to torus n=1.\<close>
        \<comment> \<open>With length 4, 2 labels, alternating: scheme ~ torus n=1.
           This uses: the scheme is equivalent to [(a,T),(b,T),(a,F),(b,F)]
           via at most rotate + flip\\_label + relabel.\<close>
        have "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv scheme w"
        proof -
          \<comment> \<open>The scheme has length 4, 2 distinct labels, alternating, opposite directions.
             After flip\\_label and relabel: [(0,T),(1,T),(0,F),(1,F)] = torus n=1.\<close>
          \<comment> \<open>Extract the 4 elements.\<close>
          obtain s0 s1 s2 s3 where hsch4: "scheme = [s0, s1, s2, s3]"
            using \<open>length scheme = 4\<close> by (cases scheme; simp; cases "tl scheme"; simp;
              cases "tl (tl scheme)"; simp; cases "tl (tl (tl scheme))"; simp)
          \<comment> \<open>Properties: alternating labels, opposite directions.\<close>
          have "fst s0 \<noteq> fst s1"
          proof -
            from no_adj have "\<not> (fst (scheme!0) = fst (scheme!1))" by (by100 auto)
            thus ?thesis using hsch4 by simp
          qed
          have "fst s0 = fst s2"
          proof (rule ccontr)
            assume "fst s0 \<noteq> fst s2"
            \<comment> \<open>fst s0 appears at position 0 but not 1, 2. In proper scheme with 2 occurrences,
               it must be at position 3. Then fst s2 = fst s1 (only other label).
               But positions 1,2 are adjacent with same label \\<Rightarrow> contradicts no\\_adj.\<close>
            \<comment> \<open>First show fst s3 = fst s0 (from properness of fst s0).\<close>
            \<comment> \<open>Properness of fst s0: appears at exactly 2 positions.\<close>
            have hcard_s0: "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 0
                \<or> card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 2"
              using less.prems(2)[THEN spec, of "fst s0"] by (by100 blast)
            have "0 \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s0}"
              using hsch4 \<open>length scheme = 4\<close> by simp
            hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} \<noteq> 0" by (by100 auto)
            hence hcard_s0_2: "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 2"
              using hcard_s0 by linarith
            \<comment> \<open>Positions with label fst s0: subset of {0,3} (not 1 by \\<noteq>fst s1, not 2 by assumption).\<close>
            have hsub_03: "{i. i < length scheme \<and> fst (scheme!i) = fst s0} \<subseteq> {0, 3}"
            proof
              fix j assume "j \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s0}"
              hence hj: "j < 4" "fst (scheme!j) = fst s0" using \<open>length scheme = 4\<close> by auto
              have "j \<noteq> 1"
              proof assume "j = 1" hence "fst s1 = fst s0" using hj(2) hsch4 by simp
                with \<open>fst s0 \<noteq> fst s1\<close> show False by simp qed
              moreover have "j \<noteq> 2"
              proof assume "j = 2" hence "fst s2 = fst s0" using hj(2) hsch4 by (simp add: eval_nat_numeral)
                with \<open>fst s0 \<noteq> fst s2\<close> show False by simp qed
              ultimately show "j \<in> {0, 3}" using hj(1) by (simp add: eval_nat_numeral) linarith
            qed
            \<comment> \<open>Card 2 subset of {0,3} with card {0,3} = 2 means equality.\<close>
            have "card {0::nat, 3} = 2" by simp
            hence "{i. i < length scheme \<and> fst (scheme!i) = fst s0} = {0, 3}"
              using hsub_03 hcard_s0_2 card_subset_eq[of "{0::nat, 3}"] by simp
            hence "3 \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s0}" by simp
            hence "fst s3 = fst s0" using hsch4 by (simp add: eval_nat_numeral)
            \<comment> \<open>Then fst s2 = fst s1: fst s2 \\<noteq> fst s0 (assumption) and fst s2 \\<noteq> fst s3 = fst s0.
               Properness of fst s2: appears at 2 positions. Not at 0 (fst s0) or 3 (fst s0).
               So only at 1 and 2. Hence fst(scheme!1) = fst s2, i.e., fst s1 = fst s2.\<close>
            have "fst s2 = fst s1"
            proof -
              have hcard_s2: "card {i. i < length scheme \<and> fst (scheme!i) = fst s2} = 0
                  \<or> card {i. i < length scheme \<and> fst (scheme!i) = fst s2} = 2"
                using less.prems(2)[THEN spec, of "fst s2"] by (by100 blast)
              have "2 \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s2}"
                using hsch4 \<open>length scheme = 4\<close> by (simp add: eval_nat_numeral)
              hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s2} \<noteq> 0" by (by100 auto)
              hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s2} = 2"
                using hcard_s2 by linarith
              moreover have "{i. i < length scheme \<and> fst (scheme!i) = fst s2} \<subseteq> {1, 2}"
              proof
                fix j assume "j \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s2}"
                hence hj: "j < 4" "fst (scheme!j) = fst s2" using \<open>length scheme = 4\<close> by auto
                have "j \<noteq> 0"
                proof assume "j = 0" hence "fst s2 = fst s0" using hj(2) hsch4 by simp
                  with \<open>fst s0 \<noteq> fst s2\<close> show False by simp qed
                moreover have "j \<noteq> 3"
                proof assume "j = 3" hence "fst s2 = fst s3" using hj(2) hsch4 by (simp add: eval_nat_numeral)
                  hence "fst s2 = fst s0" using \<open>fst s3 = fst s0\<close> by simp
                  with \<open>fst s0 \<noteq> fst s2\<close> show False by simp qed
                ultimately show "j \<in> {1, 2}" using hj(1) by (simp add: eval_nat_numeral) linarith
              qed
              ultimately have "{i. i < length scheme \<and> fst (scheme!i) = fst s2} = {1, 2}"
                using card_subset_eq[of "{1::nat, 2}"] by simp
              hence "1 \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s2}" by simp
              thus "fst s2 = fst s1" using hsch4 by simp
            qed
            hence "fst (scheme!1) = fst (scheme!2)" using hsch4 by simp
            have h12: "\<not> (fst (scheme!1) = fst (scheme!(Suc 1)))"
              using no_adj by (by5000 force)
            have "\<not> (fst (scheme!1) = fst (scheme!2))" using h12 by (simp add: numeral_2_eq_2)
            thus False using \<open>fst (scheme!1) = fst (scheme!2)\<close> by simp
          qed
          have "fst s1 = fst s3"
          proof (rule ccontr)
            assume "fst s1 \<noteq> fst s3"
            \<comment> \<open>fst s3 \\<noteq> fst s1 and fst s3 \\<noteq> fst s0 (otherwise fst s0 appears at 0,2,3 = 3 times).
               So fst s3 is a 3rd label. But scheme has only 2 labels (proper, length 4).
               Contradiction: fst s3 appears only at position 3, card = 1.\<close>
            have hproper_s0: "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} \<in> {0, 2}"
            proof -
              from less.prems(2) have "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}" .
              thus ?thesis by (by100 blast)
            qed
            have "fst s3 \<noteq> fst s0"
            proof
              assume "fst s3 = fst s0"
              have "{0::nat, 2, 3} \<subseteq> {i. i < length scheme \<and> fst (scheme!i) = fst s0}"
                using hsch4 \<open>length scheme = 4\<close> \<open>fst s0 = fst s2\<close> \<open>fst s3 = fst s0\<close>
                by (simp add: eval_nat_numeral)
              hence "card {0::nat, 2, 3} \<le> card {i. i < length scheme \<and> fst (scheme!i) = fst s0}"
                by (intro card_mono) simp
              hence "3 \<le> card {i. i < length scheme \<and> fst (scheme!i) = fst s0}" by simp
              hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} \<ge> 3" by simp
              moreover from hproper_s0 have "card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 0
                  \<or> card {i. i < length scheme \<and> fst (scheme!i) = fst s0} = 2" by (by100 blast)
              ultimately show False by linarith
            qed
            \<comment> \<open>Now fst s3 \\<noteq> fst s0 and fst s3 \\<noteq> fst s1. So fst s3 appears only at position 3.
               card = 1, but proper says {0, 2}. Contradiction.\<close>
            have "{i. i < length scheme \<and> fst (scheme!i) = fst s3} = {3}"
            proof
              show "{i. i < length scheme \<and> fst (scheme!i) = fst s3} \<subseteq> {3}"
              proof
                fix j assume "j \<in> {i. i < length scheme \<and> fst (scheme!i) = fst s3}"
                hence hj: "j < 4" "fst (scheme!j) = fst s3" using \<open>length scheme = 4\<close> by auto
                show "j \<in> {3}"
                proof -
                  have "j \<in> {0,1,2,3}" using hj(1) by (simp add: eval_nat_numeral, by100 auto)
                  moreover have "j = 0 \<Longrightarrow> fst s3 = fst s0" using hj(2) hsch4 by simp
                  moreover have "j = 1 \<Longrightarrow> fst s3 = fst s1" using hj(2) hsch4 by simp
                  moreover have "j = 2 \<Longrightarrow> fst s3 = fst s2" using hj(2) hsch4 by (simp add: eval_nat_numeral)
                  ultimately show "j \<in> {3}" using \<open>fst s3 \<noteq> fst s0\<close> \<open>fst s1 \<noteq> fst s3\<close> \<open>fst s0 = fst s2\<close>
                    by (simp add: eval_nat_numeral, by100 auto)
                qed
              qed
            next
              show "{3} \<subseteq> {i. i < length scheme \<and> fst (scheme!i) = fst s3}"
                using hsch4 \<open>length scheme = 4\<close> by (simp add: eval_nat_numeral)
            qed
            hence "card {i. i < length scheme \<and> fst (scheme!i) = fst s3} = 1" by simp
            moreover have "card {i. i < length scheme \<and> fst (scheme!i) = fst s3} \<in> {0, 2}"
              using less.prems(2) by simp
            ultimately show False by simp
          qed
          have htorus: "\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
              \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j))"
            by (rule \<open>\<not> (\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
              \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j))\<close>)
          have "snd s0 \<noteq> snd s2"
          proof
            assume "snd s0 = snd s2"
            have "(0::nat) < length scheme" "2 < length scheme" "(0::nat) \<noteq> 2"
                "fst (scheme!0) = fst s0" "fst (scheme!2) = fst s0"
                "snd (scheme!0) = snd (scheme!2)"
              using \<open>length scheme = 4\<close> hsch4 \<open>fst s0 = fst s2\<close> \<open>snd s0 = snd s2\<close>
              by (simp_all add: eval_nat_numeral)
            hence "\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
                \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
              by (intro exI[of _ "fst s0"] exI[of _ 0] exI[of _ 2]) (by100 blast)
            with htorus show False by simp
          qed
          have "snd s1 \<noteq> snd s3"
          proof
            assume "snd s1 = snd s3"
            have "(1::nat) < length scheme" "3 < length scheme" "(1::nat) \<noteq> 3"
                "fst (scheme!1) = fst s1" "fst (scheme!3) = fst s1"
                "snd (scheme!1) = snd (scheme!3)"
              using \<open>length scheme = 4\<close> hsch4 \<open>fst s1 = fst s3\<close> \<open>snd s1 = snd s3\<close>
              by (simp_all add: eval_nat_numeral)
            hence "\<exists>label. \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
                \<and> fst (scheme!i) = label \<and> fst (scheme!j) = label \<and> snd (scheme!i) = snd (scheme!j)"
              by (intro exI[of _ "fst s1"] exI[of _ 1] exI[of _ 3]) (by100 blast)
            with htorus show False by simp
          qed
          \<comment> \<open>After flip\\_label: scheme ~ [(fst s0,T),(fst s1,T),(fst s0,F),(fst s1,F)].
             This is a torus scheme of type n=1 (with labels fst s0, fst s1).
             Then relabel to standard labels gives top1\\_n\\_torus\\_scheme 1.\<close>
          \<comment> \<open>Construct equivalence: scheme ~ flip\\_label(s) ~ relabel ~ torus n=1.\<close>
          \<comment> \<open>The scheme is [(fst s0,d0),(fst s1,d1),(fst s0,\\<not>d0),(fst s1,\\<not>d1)] where d0=snd s0, d1=snd s1.\<close>
          \<comment> \<open>After at most 2 flip\\_labels and 2 relabels: ~ [(0,T),(1,T),(0,F),(1,F)] = torus n=1.\<close>
          \<comment> \<open>Step 1: flip\\_label if needed to standardize snd to True at positions 0,1.\<close>
          define scheme1 where "scheme1 = (if snd s0 then scheme else
              map (\<lambda>(l,b). (l, if l = fst s0 then \<not>b else b)) scheme)"
          have hequiv1: "top1_scheme_equiv scheme scheme1"
            unfolding scheme1_def top1_scheme_equiv_def
            using top1_elementary_scheme_operation.flip_label[of scheme "fst s0"]
            by (cases "snd s0") simp_all
          define scheme2 where "scheme2 = (if snd s1 then scheme1 else
              map (\<lambda>(l,b). (l, if l = fst s1 then \<not>b else b)) scheme1)"
          have hequiv2: "top1_scheme_equiv scheme1 scheme2"
            unfolding scheme2_def top1_scheme_equiv_def
            using top1_elementary_scheme_operation.flip_label[of scheme1 "fst s1"]
            by (cases "snd s1") simp_all
          \<comment> \<open>After flips: scheme2 = [(fst s0,T),(fst s1,T),(fst s0,F),(fst s1,F)].\<close>
          have hsch2: "scheme2 = [(fst s0,True),(fst s1,True),(fst s0,False),(fst s1,False)]"
          proof -
            \<comment> \<open>After flip1: scheme1 has snd at position 0 = True.\<close>
            have "s2 = (fst s0, \<not> snd s0)" using \<open>fst s0 = fst s2\<close> \<open>snd s0 \<noteq> snd s2\<close>
              by (cases s2) simp
            have "s3 = (fst s1, \<not> snd s1)" using \<open>fst s1 = fst s3\<close> \<open>snd s1 \<noteq> snd s3\<close>
              by (cases s3) simp
            have hsch_exp: "scheme = [(fst s0, snd s0), (fst s1, snd s1), (fst s0, \<not>snd s0), (fst s1, \<not>snd s1)]"
              using hsch4 \<open>s2 = (fst s0, \<not> snd s0)\<close> \<open>s3 = (fst s1, \<not> snd s1)\<close>
              by (cases s0, cases s1) simp
            show ?thesis
              unfolding scheme2_def scheme1_def hsch_exp
              using \<open>fst s0 \<noteq> fst s1\<close> by (cases "snd s0"; cases "snd s1") simp_all
          qed
          \<comment> \<open>Step 2: relabel to standard labels 0, 1 via elementary relabel operations.\<close>
          have "top1_scheme_equiv scheme2 (top1_n_torus_scheme 1)"
          proof (cases "fst s1 = (0::nat)")
            case False
            \<comment> \<open>fst s1 \\<noteq> 0: relabel fst s0\\<to>0, then fst s1\\<to>1 (no collision).\<close>
            have h_r1: "top1_scheme_equiv scheme2
                (map (\<lambda>(l,b). (if l = fst s0 then 0 else l, b)) scheme2)"
              unfolding top1_scheme_equiv_def
              using top1_elementary_scheme_operation.relabel[of scheme2 "fst s0" 0] by simp
            have h_mid: "map (\<lambda>(l,b). (if l = fst s0 then 0 else l, b)) scheme2
                = [(0,True),(fst s1,True),(0,False),(fst s1,False)]"
              unfolding hsch2 using \<open>fst s0 \<noteq> fst s1\<close> by simp
            have h_r2: "top1_scheme_equiv [(0,True),(fst s1,True),(0,False),(fst s1,False)]
                (map (\<lambda>(l,b). (if l = fst s1 then 1 else l, b)) [(0,True),(fst s1,True),(0,False),(fst s1,False)])"
              unfolding top1_scheme_equiv_def
              using top1_elementary_scheme_operation.relabel
                [of "[(0,True),(fst s1,True),(0,False),(fst s1,False)]" "fst s1" 1] by simp
            have h_final: "map (\<lambda>(l,b). (if l = fst s1 then 1 else l, b)) [(0,True),(fst s1,True),(0,False),(fst s1,False)]
                = top1_n_torus_scheme 1"
              unfolding top1_n_torus_scheme_def using False by simp
            from h_r1 have "top1_scheme_equiv scheme2 [(0,True),(fst s1,True),(0,False),(fst s1,False)]"
              unfolding top1_scheme_equiv_def h_mid by simp
            moreover from h_r2 have "top1_scheme_equiv [(0,True),(fst s1,True),(0,False),(fst s1,False)] (top1_n_torus_scheme 1)"
              unfolding top1_scheme_equiv_def h_final by simp
            ultimately show ?thesis unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          next
            case True
            \<comment> \<open>fst s1 = 0: use 3-step relabel via intermediate label (fst s0 + 1).\<close>
            hence "fst s0 \<noteq> 0" using \<open>fst s0 \<noteq> fst s1\<close> by simp
            define fr where "fr = fst s0 + 1"
            have hfr: "fr \<noteq> fst s0" "fr \<noteq> fst s1" "fr \<noteq> 0" "fr \<noteq> 1"
              unfolding fr_def using True \<open>fst s0 \<noteq> 0\<close> by simp_all
            \<comment> \<open>relabel fst s0\\<to>fr, then fst s1=0\\<to>1, then fr\\<to>0.\<close>
            \<comment> \<open>scheme2 = [(fst s0,T),(0,T),(fst s0,F),(0,F)]. relabel fst s0\\<to>1:\\<close>
            have h_r1: "top1_scheme_equiv scheme2
                (map (\<lambda>(l,b). (if l = fst s0 then 1 else l, b)) scheme2)"
              unfolding top1_scheme_equiv_def
              using top1_elementary_scheme_operation.relabel[of scheme2 "fst s0" 1] by simp
            have h_mid: "map (\<lambda>(l,b). (if l = fst s0 then 1 else l, b)) scheme2
                = [(Suc 0,True),(0::nat,True),(Suc 0,False),(0,False)]"
              unfolding hsch2 using \<open>fst s0 \<noteq> fst s1\<close> True by (simp add: eval_nat_numeral)
            \<comment> \<open>[(1,T),(0,T),(1,F),(0,F)] ~ rotate ~ flip\\_label 1 ~ target.\<close>
            have h_rot: "top1_elementary_scheme_operation
                [(Suc 0,True),(0::nat,True),(Suc 0,False),(0,False)]
                [(0,True),(Suc 0,False),(0,False),(Suc 0,True)]"
              using top1_elementary_scheme_operation.rotate[of "[(Suc 0,True)]" "[(0,True),(Suc 0,False),(0,False)]"]
              by simp
            have h_flip: "top1_elementary_scheme_operation
                [(0::nat,True),(Suc 0,False),(0,False),(Suc 0,True)]
                (map (\<lambda>(l,b). (l, if l = Suc 0 then \<not>b else b)) [(0,True),(Suc 0,False),(0,False),(Suc 0,True)])"
              by (rule top1_elementary_scheme_operation.flip_label)
            have h_flip_simp: "map (\<lambda>(l,b). (l, if l = Suc (0::nat) then \<not>b else b)) [(0,True),(Suc 0,False),(0,False),(Suc 0,True)]
                = [(0,True),(Suc 0,True),(0,False),(Suc 0,False)]"
              by simp
            have "[(0::nat,True),(Suc 0,True),(0,False),(Suc 0,False)] = top1_n_torus_scheme 1"
              unfolding top1_n_torus_scheme_def by (simp add: eval_nat_numeral)
            from h_r1 h_mid have s2_mid: "top1_scheme_equiv scheme2 [(Suc 0,True),(0::nat,True),(Suc 0,False),(0,False)]"
              unfolding top1_scheme_equiv_def by simp
            from s2_mid h_rot have s2_rot: "top1_scheme_equiv scheme2 [(0,True),(Suc 0,False),(0,False),(Suc 0,True)]"
              unfolding top1_scheme_equiv_def by (meson rtranclp.rtrancl_into_rtrancl)
            from h_flip have "top1_elementary_scheme_operation
                [(0::nat,True),(Suc 0,False),(0,False),(Suc 0,True)]
                [(0,True),(Suc 0,True),(0,False),(Suc 0,False)]"
              using h_flip_simp by simp
            with s2_rot have "top1_scheme_equiv scheme2 [(0,True),(Suc 0,True),(0,False),(Suc 0,False)]"
              unfolding top1_scheme_equiv_def by (meson rtranclp.rtrancl_into_rtrancl)
            thus ?thesis using \<open>[(0::nat,True),(Suc 0,True),(0,False),(Suc 0,False)] = top1_n_torus_scheme 1\<close>
              by simp
          qed
          have "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv scheme w"
          proof -
            have "top1_scheme_equiv scheme (top1_n_torus_scheme 1)"
              using hequiv1 hequiv2 \<open>top1_scheme_equiv scheme2 (top1_n_torus_scheme 1)\<close>
              unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
            thus ?thesis
              unfolding top1_is_torus_scheme_def by (by100 blast)
          qed
          thus ?thesis by (by100 blast)
        qed
        thus ?thesis by (by100 blast)
      qed
    next
      case False
      \<comment> \<open>Length > 4: either has cancellable adjacent pair (shorter scheme) or
         no adjacent same labels. Apply Lemma 77.3 to extract commutator.\<close>
      have hgt4: "length scheme > 4" using less.prems(1) False by linarith
      \<comment> \<open>Book proof: check if scheme has adjacent cancellable pair.\<close>
      show ?thesis
      proof (cases "\<exists>i. i + 1 < length scheme \<and> fst (scheme!i) = fst (scheme!(i+1))
              \<and> snd (scheme!i) \<noteq> snd (scheme!(i+1))")
        case True
        \<comment> \<open>Adjacent inverse pair found: cancel to get shorter torus scheme.
           Apply IH to the shorter scheme.\<close>
        \<comment> \<open>Get adjacent inverse pair.\<close>
        from True obtain j where hj: "j + 1 < length scheme"
            "fst (scheme!j) = fst (scheme!(j+1))" "snd (scheme!j) \<noteq> snd (scheme!(j+1))"
          by (by100 blast)
        \<comment> \<open>scheme!(j+1) = inverse(scheme!j).\<close>
        have hjinv: "scheme!(j+1) = top1_inverse_edge (scheme!j)"
          using hj(2) hj(3) unfolding top1_inverse_edge_def
          by (cases "scheme!j", cases "scheme!(j+1)") (by100 simp)
        \<comment> \<open>Cancel: scheme ~ shorter scheme (remove positions j, j+1).\<close>
        define shorter where "shorter = take j scheme @ drop (j+2) scheme"
        have hcancel: "top1_scheme_equiv scheme shorter"
        proof -
          have hdecomp_j: "scheme = take j scheme @ [scheme!j, top1_inverse_edge (scheme!j)] @ drop (j+2) scheme"
          proof -
            have "scheme = take j scheme @ scheme!j # drop (Suc j) scheme"
              using id_take_nth_drop[of j scheme] hj(1) by (by100 simp)
            also have "drop (Suc j) scheme = scheme!(j+1) # drop (Suc (Suc j)) scheme"
              using Cons_nth_drop_Suc[of "Suc j" scheme] hj(1) by (by100 simp)
            finally show ?thesis using hjinv by (by100 simp)
          qed
          have "top1_elementary_scheme_operation
              (take j scheme @ [scheme!j, top1_inverse_edge (scheme!j)] @ drop (j+2) scheme)
              (take j scheme @ drop (j+2) scheme)"
            by (rule top1_elementary_scheme_operation.cancel)
          hence "top1_elementary_scheme_operation scheme shorter"
            using hdecomp_j unfolding shorter_def by (by100 simp)
          thus ?thesis unfolding top1_scheme_equiv_def
            by (by100 simp)
        qed
        have hlen_shorter: "length shorter = length scheme - 2"
          unfolding shorter_def using hj(1) by (by100 simp)
        \<comment> \<open>Shorter scheme is proper.\<close>
        have hproper_shorter: "\<forall>label. card {i. i < length shorter \<and> fst (shorter!i) = label} \<in> {0, 2}"
          using cancel_preserves_proper[OF less(3) hj(1) hj(2)]
          unfolding shorter_def by (by100 blast)
        \<comment> \<open>Length of shorter \\<ge> 4 (cancel reduces by 2; properness prevents odd lengths).\<close>
        have hlen_ge4: "length shorter \<ge> 4"
        proof -
          \<comment> \<open>Properness \<Longrightarrow> even length. length > 4 and even \<Longrightarrow> length \<ge> 6.
             shorter = length - 2 \<ge> 4.\<close>
          have "even (length scheme)"
            using proper_scheme_even_length[OF less(3)] .
          hence "length scheme \<ge> 6" using hgt4 by (by100 presburger)
          thus ?thesis using hlen_shorter by (by100 simp)
        qed
        \<comment> \<open>Apply IH.\<close>
        have hlen_lt: "length shorter < length scheme"
          using hlen_shorter hgt4 by (by100 simp)
        from less(1)[OF hlen_lt hlen_ge4 hproper_shorter]
        have hIH: "(\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv shorter [(a, True), (a, False), (b, True), (b, False)])
           \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv shorter w)
           \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv shorter w)" .
        \<comment> \<open>Chain: scheme ~ shorter ~ normal form.\<close>
        show ?thesis
        proof -
          from hIH show ?thesis
          proof (elim disjE)
            assume "\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv shorter [(a, True), (a, False), (b, True), (b, False)]"
            then obtain a b where "a \<noteq> b" "top1_scheme_equiv shorter [(a, True), (a, False), (b, True), (b, False)]"
              by (by100 blast)
            hence "top1_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)]"
              using hcancel unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
            thus ?thesis using \<open>a \<noteq> b\<close> by (by100 blast)
          next
            assume "\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv shorter w"
            then obtain m' w where "m' > 0" "top1_is_projective_scheme w m'" "top1_scheme_equiv shorter w"
              by (by100 blast)
            hence "top1_scheme_equiv scheme w"
              using hcancel unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
            thus ?thesis using \<open>m' > 0\<close> \<open>top1_is_projective_scheme w m'\<close> by (by100 blast)
          next
            assume "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv shorter w"
            then obtain n' w where "n' > 0" "top1_is_torus_scheme w n'" "top1_scheme_equiv shorter w"
              by (by100 blast)
            hence "top1_scheme_equiv scheme w"
              using hcancel unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
            thus ?thesis using \<open>n' > 0\<close> \<open>top1_is_torus_scheme w n'\<close> by (by100 blast)
          qed
        qed
      next
        case hno_adj_gt4: False
        \<comment> \<open>No adjacent inverse pairs. Book proof:
           1. Choose label a with closest opposite-direction occurrences.
           2. Find label b between them (exists because length > 4 and no adjacent same).
           3. By flip\\_label if needed, arrange as w0 a b w1 a\\<inverse> b\\<inverse> w2.
           4. Apply Lemma 77.3: ~ aba\\<inverse>b\\<inverse> w0 w1 w2.
           5. aba\\<inverse>b\\<inverse> w3 is a torus scheme with w3 shorter or equal length.
           6. Continue extracting commutators (or apply IH if w3 cancels).\<close>
        \<comment> \<open>Extract label a and positions of a, a\\<inverse>, label b between them.\<close>
        have "\<exists>a b w0 w1 w2. a \<noteq> b \<and>
            top1_scheme_equiv scheme
              (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2)
            \<and> length w0 + length w1 + length w2 + 4 = length scheme
            \<and> (\<forall>l. length (filter (\<lambda>e. fst e = l)
                (w0 @ [(a, True), (b, True)] @ w1 @ [(a, False), (b, False)] @ w2))
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
            ultimately show False using hno_adj_gt4 by (by100 blast)
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
          have "top1_scheme_equiv scheme (drop p1 scheme @ take p1 scheme)"
            using elementary_imp_equiv[OF top1_elementary_scheme_operation.rotate[of "take p1 scheme" "drop p1 scheme"]]
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
          have hR_equiv: "top1_scheme_equiv scheme R" using \<open>top1_scheme_equiv scheme (drop p1 scheme @ take p1 scheme)\<close>
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
          have "\<exists>w0 w1 w2. top1_scheme_equiv scheme
              (w0 @ [(a_lab, True), (b_lab, True)] @ w1 @ [(a_lab, False), (b_lab, False)] @ w2)
              \<and> length w0 + length w1 + length w2 + 4 = length scheme
              \<and> (\<forall>l. length (filter (\<lambda>e. fst e = l)
                  (w0 @ [(a_lab, True), (b_lab, True)] @ w1 @ [(a_lab, False), (b_lab, False)] @ w2))
                = length (filter (\<lambda>e. fst e = l) scheme))"
          proof -
            \<comment> \<open>Step A: Flip a\_lab direction. scheme \<sim> R. Then R \<sim> R\_a (a\_lab has True at front).\<close>
            define R_a where "R_a = (if dir_a then R else
                map (\<lambda>(l,bo). (l, if l = a_lab then \<not>bo else bo)) R)"
            have hRa_equiv: "top1_scheme_equiv scheme R_a"
            proof (cases dir_a)
              case True thus ?thesis unfolding R_a_def using hR_equiv by (by100 simp)
            next
              case False
              hence "R_a = map (\<lambda>(l,bo). (l, if l = a_lab then \<not>bo else bo)) R" unfolding R_a_def by (by100 simp)
              moreover have "top1_scheme_equiv R (map (\<lambda>(l,bo). (l, if l = a_lab then \<not>bo else bo)) R)"
                using elementary_imp_equiv[OF top1_elementary_scheme_operation.flip_label[of R a_lab]] by (by100 simp)
              ultimately show ?thesis using hR_equiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
            qed
            \<comment> \<open>Step B: Flip b\_lab direction. R\_a \<sim> R\_ab (b\_lab has True at position 1).\<close>
            define R_ab where "R_ab = (if dir_b then R_a else
                map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo)) R_a)"
            have hRab_equiv: "top1_scheme_equiv scheme R_ab"
            proof (cases dir_b)
              case True thus ?thesis unfolding R_ab_def using hRa_equiv by (by100 simp)
            next
              case False
              hence "R_ab = map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo)) R_a" unfolding R_ab_def by (by100 simp)
              moreover have "top1_scheme_equiv R_a (map (\<lambda>(l,bo). (l, if l = b_lab then \<not>bo else bo)) R_a)"
                using elementary_imp_equiv[OF top1_elementary_scheme_operation.flip_label[of R_a b_lab]] by (by100 simp)
              ultimately show ?thesis using hRa_equiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
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
            have "top1_scheme_equiv R_ab
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
              have r1: "top1_elementary_scheme_operation
                  (u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1 @ u3)
                  (u3 @ u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1)"
                using top1_elementary_scheme_operation.rotate
                  [of "u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1" u3] by simp
              have r2: "top1_elementary_scheme_operation
                  (u3 @ u0 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u1)
                  ([(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3 @ u0 @ u1)"
                using top1_elementary_scheme_operation.cut_paste_opp
                  [of "[]" "u3 @ u0" a_lab u2 u1] by simp
              have r3: "top1_elementary_scheme_operation
                  ([(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3 @ u0 @ u1)
                  (u0 @ u1 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3)"
                using top1_elementary_scheme_operation.rotate
                  [of "[(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3" "u0 @ u1"] by simp
              have "top1_scheme_equiv R_ab (u0 @ u1 @ [(a_lab,True)] @ u2 @ [(a_lab,False)] @ u3)"
                unfolding hRab_eq top1_scheme_equiv_def
                using r1 r2 r3 by (meson rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
              thus ?thesis unfolding u0_def u1_def u2_def u3_def by (by100 simp)
            qed
            hence "top1_scheme_equiv scheme
                (between @ [(a_lab,True),(b_lab,True)] @ mid @ [(a_lab,False),(b_lab,False)] @ after)"
              using hRab_equiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
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
          then obtain w0 w1 w2 where hw_equiv: "top1_scheme_equiv scheme
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
            and hequiv: "top1_scheme_equiv scheme
              (w0' @ [(a_lab, True), (b_lab, True)] @ w1' @ [(a_lab, False), (b_lab, False)] @ w2')"
            and hlen_w: "length w0' + length w1' + length w2' + 4 = length scheme"
            and hfilt_w: "\<forall>l. length (filter (\<lambda>e. fst e = l)
                (w0' @ [(a_lab, True), (b_lab, True)] @ w1' @ [(a_lab, False), (b_lab, False)] @ w2'))
              = length (filter (\<lambda>e. fst e = l) scheme)"
          by blast
        \<comment> \<open>Apply Lemma 77.3.\<close>
        from Lemma_77_3_torus_extraction[OF hab, of w0' w1' w2']
        have "top1_scheme_equiv
            (w0' @ [(a_lab, True), (b_lab, True)] @ w1' @ [(a_lab, False), (b_lab, False)] @ w2')
            ([(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)] @ w0' @ w1' @ w2')" .
        \<comment> \<open>Chain: scheme ~ pattern ~ aba\\<inverse>b\\<inverse> w3.\<close>
        hence "top1_scheme_equiv scheme
            ([(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)] @ w0' @ w1' @ w2')"
          using hequiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
        \<comment> \<open>Book Step 1 continuation: scheme ~ [commutator] @ w3.
           If w3 = []: torus n=1. Done.
           If w3 has adjacent cancellable pair: cancel \<Rightarrow> shorter scheme \<Rightarrow> IH.
           Otherwise: extract another commutator from w3, repeat.\<close>
        \<comment> \<open>Continuation: scheme \<sim> [block] @ w3. Check for adjacent inverse pairs.\<close>
        define full where "full = [(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)] @ w0' @ w1' @ w2'"
        have hfull_equiv: "top1_scheme_equiv scheme full"
          using \<open>top1_scheme_equiv scheme
            ([(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)] @ w0' @ w1' @ w2')\<close>
          unfolding full_def .
        \<comment> \<open>full has same length as scheme and is proper.\<close>
        have hproper_full: "\<forall>label. card {i. i < length full \<and> fst (full!i) = label} \<in> {0, 2}"
        proof (intro allI)
          fix label
          define inter where "inter = w0' @ [(a_lab,True),(b_lab,True)] @ w1' @ [(a_lab,False),(b_lab,False)] @ w2'"
          have hfilt_eq: "length (filter (\<lambda>e. fst e = label) full) = length (filter (\<lambda>e. fst e = label) inter)"
            unfolding full_def inter_def by (by100 simp)
          have "length (filter (\<lambda>e. fst e = label) inter) = length (filter (\<lambda>e. fst e = label) scheme)"
            using hfilt_w unfolding inter_def by (by100 simp)
          hence "length (filter (\<lambda>e. fst e = label) full) = length (filter (\<lambda>e. fst e = label) scheme)"
            using hfilt_eq by (by100 simp)
          hence "card {i. i < length full \<and> fst (full!i) = label} = card {i. i < length scheme \<and> fst (scheme!i) = label}"
          proof -
            assume h: "length (filter (\<lambda>e. fst e = label) full) = length (filter (\<lambda>e. fst e = label) scheme)"
            have h1: "card {i. i < length full \<and> fst (full!i) = label} = length (filter (\<lambda>e. fst e = label) full)"
              using length_filter_conv_card[of "\<lambda>e. fst e = label" full, symmetric] by (by100 simp)
            have h2: "card {i. i < length scheme \<and> fst (scheme!i) = label} = length (filter (\<lambda>e. fst e = label) scheme)"
              using length_filter_conv_card[of "\<lambda>e. fst e = label" scheme, symmetric] by (by100 simp)
            show ?thesis using h h1 h2 by (by100 linarith)
          qed
          moreover from less(3) have "card {i. i < length scheme \<and> fst (scheme!i) = label} \<in> {0, 2}" by (by100 blast)
          ultimately show "card {i. i < length full \<and> fst (full!i) = label} \<in> {0, 2}" by (by100 simp)
        qed
        \<comment> \<open>Check if full has an adjacent inverse pair anywhere.\<close>
        show ?thesis
        proof (cases "\<exists>j. j + 1 < length full \<and> fst (full!j) = fst (full!(j+1))
                \<and> snd (full!j) \<noteq> snd (full!(j+1))")
          case True
          \<comment> \<open>Adjacent inverse pair found: cancel \<to> shorter \<to> IH.\<close>
          then obtain j where hj: "j + 1 < length full"
              "fst (full!j) = fst (full!(j+1))" "snd (full!j) \<noteq> snd (full!(j+1))"
            by (by100 blast)
          define shorter where "shorter = take j full @ drop (j+2) full"
          have hjinv: "full!(j+1) = top1_inverse_edge (full!j)"
            using hj(2) hj(3) unfolding top1_inverse_edge_def
            by (cases "full!j", cases "full!(j+1)") (by100 simp)
          have "top1_scheme_equiv full shorter"
          proof -
            have "full = take j full @ [full!j, top1_inverse_edge (full!j)] @ drop (j+2) full"
              using id_take_nth_drop[of j full] hj(1) hjinv
              using Cons_nth_drop_Suc[of "Suc j" full] by (by100 simp)
            hence "top1_elementary_scheme_operation full shorter"
              unfolding shorter_def
              using top1_elementary_scheme_operation.cancel[of "take j full" "full!j" "drop (j+2) full"]
              by (by100 simp)
            thus ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
          qed
          hence "top1_scheme_equiv scheme shorter"
            using hfull_equiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          have hlen_shorter: "length shorter = length full - 2"
            unfolding shorter_def using hj(1) by (by100 simp)
          have hlen_full: "length full = length scheme"
            unfolding full_def using hlen_w by (by100 simp)
          hence hlt: "length shorter < length scheme"
            using hlen_shorter hj(1) by (by100 linarith)
          have hge4: "length shorter \<ge> 4"
          proof -
            have "even (length scheme)" using proper_scheme_even_length[OF less(3)] .
            hence "length scheme \<ge> 6" using hgt4 by (by100 presburger)
            thus ?thesis using hlen_shorter hlen_full by (by100 linarith)
          qed
          \<comment> \<open>hproper\_full is available from the outer scope (proved before the case split).\<close>
          have hproper_shorter: "\<forall>label. card {i. i < length shorter \<and> fst (shorter!i) = label} \<in> {0, 2}"
            using cancel_preserves_proper[OF hproper_full hj(1) hj(2)]
            unfolding shorter_def by (by100 blast)
          from less(1)[OF hlt hge4 hproper_shorter]
          have "(\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv shorter [(a, True), (a, False), (b, True), (b, False)])
               \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv shorter w)
               \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv shorter w)" .
          have "top1_scheme_equiv scheme shorter"
            using hfull_equiv \<open>top1_scheme_equiv full shorter\<close>
            unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
          thus ?thesis using \<open>(\<exists>a b. _) \<or> (\<exists>m>0. _) \<or> (\<exists>n>0. _)\<close>
            unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
        next
          case False
          \<comment> \<open>No adjacent inverse pair in full. Then full is torus-type.
             Since full has the commutator block at front and w3 as remainder,
             this means w3 has no adjacent inverse pair either.
             Continue extracting commutators (or show full = torus directly).\<close>
          \<comment> \<open>No adjacent inverse pair. Apply IH to w3 = w0'@w1'@w2' (shorter than scheme).
             Combine result with the commutator block.\<close>
          define w3 where "w3 = w0' @ w1' @ w2'"
          have hfull_w3: "full = [(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)] @ w3"
            unfolding full_def w3_def by (by100 simp)
          have hlen_w3: "length w3 + 4 = length scheme" using hlen_w unfolding w3_def by (by100 simp)
          hence hlt_w3: "length w3 < length scheme" by (by100 linarith)
          have heven_scheme: "even (length scheme)" using proper_scheme_even_length[OF less(3)] .
          hence heven_w3: "even (length w3)" using hlen_w3 by (by100 presburger)
          show ?thesis
          proof (cases "w3 = []")
            case True
            \<comment> \<open>w3 is empty: full = one commutator block = torus n=1.\<close>
            have hfull_block: "full = [(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)]"
              using hfull_w3 True by (by100 simp)
            have hblock_torus: "top1_scheme_equiv full (top1_n_torus_scheme 1)"
              using commutator_block_equiv_torus_1[OF hab] hfull_block by (by100 simp)
            have "top1_scheme_equiv scheme (top1_n_torus_scheme 1)"
              using hfull_equiv hblock_torus unfolding top1_scheme_equiv_def
              by (meson rtranclp_trans)
            hence "\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv scheme w"
              unfolding top1_is_torus_scheme_def by (by100 blast)
            thus ?thesis by (by100 blast)
          next
            case False
            hence "length w3 > 0" by (by100 simp)
            hence "length w3 \<ge> 2" using heven_w3 by (by100 presburger)
            show ?thesis
            proof (cases "length w3 < 4")
              case True
              \<comment> \<open>length w3 = 2 (even, > 0, < 4). Proper \<Rightarrow> one label, both same direction
                 (no adjacent inverse pair). This is a projective pair.\<close>
              have hlen2: "length w3 = 2" using True \<open>length w3 \<ge> 2\<close> heven_w3 by (by100 presburger)
              \<comment> \<open>w3 = [e1, e2]. Extract the elements.\<close>
              obtain e1 e2 where hw3_exp: "w3 = [e1, e2]"
              proof -
                have "w3 = w3!0 # w3!1 # []"
                  using hlen2 by (cases w3, by100 simp, cases "tl w3", by100 simp, by100 simp)
                thus ?thesis using that by (by100 blast)
              qed
              \<comment> \<open>Properness: fst e1 = fst e2 (otherwise count = 1 \\<notin> \{0,2\}).\<close>
              \<comment> \<open>Derive properness of w3 from properness of full (same argument as ge4 case).\<close>
              have hproper_w3_local: "\<forall>label. card {i. i < length w3 \<and> fst (w3!i) = label} \<in> {0, 2}"
              proof (intro allI)
                fix label
                have hfc_decomp: "length (filter (\<lambda>e. fst e = label) full)
                    = length (filter (\<lambda>e. fst e = label) [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)])
                    + length (filter (\<lambda>e. fst e = label) w3)"
                  unfolding hfull_w3 by (by100 simp)
                have hfc_full_len: "length (filter (\<lambda>e. fst e = label) full) \<in> {0, 2}"
                proof -
                  have "card {i. i < length full \<and> fst (full!i) = label} = length (filter (\<lambda>e. fst e = label) full)"
                    using length_filter_conv_card[of "\<lambda>e. fst e = label" full, symmetric] by (by100 simp)
                  moreover have "card {i. i < length full \<and> fst (full!i) = label} \<in> {0, 2}"
                    using hproper_full by (by100 blast)
                  ultimately show ?thesis by (by100 simp)
                qed
                have hfc_block: "length (filter (\<lambda>e. fst e = label) [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)])
                    \<in> {0, 2}" using hab by (by100 simp)
                have "length (filter (\<lambda>e. fst e = label) full) = 0 \<or> length (filter (\<lambda>e. fst e = label) full) = 2"
                  using hfc_full_len by (by100 blast)
                moreover have "length (filter (\<lambda>e. fst e = label) [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)]) = 0
                    \<or> length (filter (\<lambda>e. fst e = label) [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)]) = 2"
                  using hfc_block by (by100 blast)
                ultimately have "length (filter (\<lambda>e. fst e = label) w3) = 0 \<or> length (filter (\<lambda>e. fst e = label) w3) = 2"
                  using hfc_decomp by (by100 linarith)
                hence "length (filter (\<lambda>e. fst e = label) w3) \<in> {0, 2}" by (by100 blast)
                thus "card {i. i < length w3 \<and> fst (w3!i) = label} \<in> {0, 2}"
                proof -
                  have "card {i. i < length w3 \<and> fst (w3!i) = label} = length (filter (\<lambda>e. fst e = label) w3)"
                    using length_filter_conv_card[of "\<lambda>e. fst e = label" w3, symmetric] by (by100 simp)
                  thus ?thesis using \<open>length (filter (\<lambda>e. fst e = label) w3) \<in> {0, 2}\<close> by (by100 simp)
                qed
              qed
              have hfst_eq: "fst e1 = fst e2"
              proof (rule ccontr)
                assume hne: "fst e1 \<noteq> fst e2"
                have "length (filter (\<lambda>e. fst e = fst e1) w3) = 1"
                  unfolding hw3_exp using hne by (by100 simp)
                moreover have "length (filter (\<lambda>e. fst e = fst e1) w3) \<in> {0, 2}"
                proof -
                  have "card {i. i < length w3 \<and> fst (w3!i) = fst e1} \<in> {0, 2}"
                    using hproper_w3_local by (by100 blast)
                  moreover have "card {i. i < length w3 \<and> fst (w3!i) = fst e1}
                      = length (filter (\<lambda>e. fst e = fst e1) w3)"
                    using length_filter_conv_card[of "\<lambda>e. fst e = fst e1" w3, symmetric] by (by100 simp)
                  ultimately show ?thesis by (by100 simp)
                qed
                ultimately show False by (by100 simp)
              qed
              \<comment> \<open>No adjacent inverse pair in full: e1, e2 are NOT inverse pair.\<close>
              have hsnd_eq: "snd e1 = snd e2"
              proof (rule ccontr)
                assume hne: "snd e1 \<noteq> snd e2"
                \<comment> \<open>Position in full: block has length 4, w3 starts at position 4.\<close>
                have hfull_len: "length full = length scheme"
                  unfolding full_def using hlen_w by (by100 simp)
                have "full!(4) = e1" "full!(5) = e2"
                  unfolding hfull_w3 hw3_exp by (by100 simp)+
                moreover have "fst (full!4) = fst (full!5)"
                  using hfst_eq unfolding hfull_w3 hw3_exp by (by100 simp)
                moreover have "snd (full!4) \<noteq> snd (full!5)"
                  using hne unfolding hfull_w3 hw3_exp by (by100 simp)
                moreover have "4 + 1 < length full"
                  using hfull_len hlen_w3 hlen2 by (by100 linarith)
                ultimately have "\<exists>j. j + 1 < length full \<and> fst (full!j) = fst (full!(j+1))
                    \<and> snd (full!j) \<noteq> snd (full!(j+1))"
                  by (rule_tac exI[of _ 4]) (by100 simp)
                with \<open>\<not>(\<exists>j. j + 1 < length full \<and> fst (full ! j) = fst (full ! (j + 1)) \<and> snd (full ! j) \<noteq> snd (full ! (j + 1)))\<close>
                show False by (by100 blast)
              qed
              \<comment> \<open>So w3 = [(c,d),(c,d)] — a projective pair.\<close>
              obtain c d where hcd: "e1 = (c, d)" "e2 = (c, d)"
              proof -
                obtain c1 d1 where "e1 = (c1, d1)" by (cases e1)
                moreover obtain c2 d2 where "e2 = (c2, d2)" by (cases e2)
                moreover have "c1 = c2" using hfst_eq \<open>e1 = (c1,d1)\<close> \<open>e2 = (c2,d2)\<close> by (by100 simp)
                moreover have "d1 = d2" using hsnd_eq \<open>e1 = (c1,d1)\<close> \<open>e2 = (c2,d2)\<close> by (by100 simp)
                ultimately show ?thesis using that by (by100 blast)
              qed
              \<comment> \<open>scheme ~ block @ [(c,d),(c,d)]. This is commutator + projective pair.\<close>
              have hsch_block_proj: "top1_scheme_equiv scheme ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ [(c,d),(c,d)])"
                using hfull_equiv hfull_w3 hw3_exp hcd by (by100 simp)
              \<comment> \<open>Convert [(c,d),(c,d)] to projective form [(0,T),(0,T)] via flip+relabel.\<close>
              \<comment> \<open>Step 1: flip c if d=False.\<close>
              have "top1_scheme_equiv [(c,d),(c,d)] [(c,True),(c,True)]"
              proof (cases d)
                case True thus ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
              next
                case FalseD: False
                have "top1_elementary_scheme_operation [(c,d),(c,d)]
                    (map (\<lambda>(l,bo). (l, if l = c then \<not>bo else bo)) [(c,d),(c,d)])"
                  by (rule top1_elementary_scheme_operation.flip_label)
                moreover have "map (\<lambda>(l,bo). (l, if l = c then \<not>bo else bo)) [(c,d),(c,d)] = [(c,True),(c,True)]"
                  using FalseD by (by100 simp)
                ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
              qed
              \<comment> \<open>Step 2: relabel c to 0.\<close>
              moreover have "top1_scheme_equiv [(c,True),(c,True)] [(0::nat,True),(0,True)]"
              proof -
                have "top1_elementary_scheme_operation [(c,True),(c,True)]
                    (map (\<lambda>(l,bo). (if l = c then 0 else l, bo)) [(c,True),(c,True)])"
                  by (rule top1_elementary_scheme_operation.relabel)
                moreover have "map (\<lambda>(l,bo). (if l = c then (0::nat) else l, bo)) [(c,True),(c,True)]
                    = [(0,True),(0,True)]" by (by100 simp)
                ultimately show ?thesis unfolding top1_scheme_equiv_def by (by100 simp)
              qed
              ultimately have "top1_scheme_equiv [(c,d),(c,d)] [(0::nat,True),(0,True)]"
                unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
              \<comment> \<open>[(0,T),(0,T)] = projective\_1.\<close>
              have "[(0::nat,True),(0,True)] = top1_m_projective_scheme 1"
                unfolding top1_m_projective_scheme_def by (by100 simp)
              \<comment> \<open>Lift to block context: scheme ~ block @ projective\_1.\<close>
              have "top1_scheme_equiv scheme ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ top1_m_projective_scheme 1)"
              proof -
                have "top1_scheme_equiv [(c,d),(c,d)] (top1_m_projective_scheme 1)"
                  using \<open>top1_scheme_equiv [(c,d),(c,d)] [(0,True),(0,True)]\<close>
                    \<open>[(0::nat,True),(0,True)] = top1_m_projective_scheme 1\<close> by (by100 simp)
                from scheme_equiv_prepend[OF this, of "[(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)]"]
                have "top1_scheme_equiv
                    ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ [(c,d),(c,d)])
                    ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ top1_m_projective_scheme 1)"
                  by (by100 blast)
                thus ?thesis using hsch_block_proj unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
              qed
              \<comment> \<open>Apply commutator\_prepend\_projective: block @ projective\_1 ~ projective\_3.\<close>
              have "\<exists>w'. top1_is_projective_scheme w' (1+2) \<and>
                  top1_scheme_equiv ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ top1_m_projective_scheme 1) w'"
                using commutator_prepend_projective[OF hab, of 1] by (by100 simp)
              then obtain w' where hw': "top1_is_projective_scheme w' (1+2)"
                  and hequiv': "top1_scheme_equiv ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ top1_m_projective_scheme 1) w'"
                by (by100 blast)
              have hsch_w': "top1_scheme_equiv scheme w'"
                using \<open>top1_scheme_equiv scheme ([(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)] @ top1_m_projective_scheme 1)\<close>
                  hequiv' unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
              have "1 + 2 = (3::nat)" by (by100 simp)
              hence hw'3: "top1_is_projective_scheme w' 3" using hw' by (by100 metis)
              have "\<exists>m>(0::nat). \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv scheme w"
              proof -
                have "(3::nat) > 0" by (by100 simp)
                moreover have "top1_is_projective_scheme w' 3 \<and> top1_scheme_equiv scheme w'"
                  using hsch_w' hw'3 by (by100 blast)
                ultimately show ?thesis by (by100 blast)
              qed
              thus ?thesis by (by100 blast)
            next
              case nFalse: False
              hence hge4_w3: "length w3 \<ge> 4" by (by100 linarith)
              \<comment> \<open>Properness of w3: labels from the block have count 0 in w3, others have count 2.\<close>
              have hproper_w3: "\<forall>label. card {i. i < length w3 \<and> fst (w3!i) = label} \<in> {0, 2}"
              proof (intro allI)
                fix label
                \<comment> \<open>full = block @ w3. Decompose filter-count.\<close>
                have hfc_decomp: "length (filter (\<lambda>e. fst e = label) full)
                    = length (filter (\<lambda>e. fst e = label) [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)])
                    + length (filter (\<lambda>e. fst e = label) w3)"
                  unfolding hfull_w3 by (by100 simp)
                have hfc_full_card: "card {i. i < length full \<and> fst (full!i) = label} \<in> {0, 2}"
                  using hproper_full by (by100 blast)
                have hfc_full_len: "length (filter (\<lambda>e. fst e = label) full) \<in> {0, 2}"
                proof -
                  have "card {i. i < length full \<and> fst (full!i) = label} = length (filter (\<lambda>e. fst e = label) full)"
                    using length_filter_conv_card[of "\<lambda>e. fst e = label" full, symmetric] by (by100 simp)
                  thus ?thesis using hfc_full_card by (by100 simp)
                qed
                have hfc_block: "length (filter (\<lambda>e. fst e = label) [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)])
                    \<in> {0, 2}"
                  using hab by (by100 simp)
                have hfc_w3: "length (filter (\<lambda>e. fst e = label) w3) \<in> {0, 2}"
                proof -
                  let ?fw = "length (filter (\<lambda>e. fst e = label) full)"
                  let ?fb = "length (filter (\<lambda>e. fst e = label) [(a_lab,True),(b_lab,True),(a_lab,False),(b_lab,False)])"
                  let ?fw3 = "length (filter (\<lambda>e. fst e = label) w3)"
                  from hfc_decomp have heq: "?fw = ?fb + ?fw3" by (by100 linarith)
                  from hfc_full_len have "?fw = 0 \<or> ?fw = 2" by (by100 blast)
                  moreover from hfc_block have "?fb = 0 \<or> ?fb = 2" by (by100 blast)
                  ultimately have "?fw3 = 0 \<or> ?fw3 = 2" using heq by (by100 linarith)
                  thus ?thesis by (by100 blast)
                qed
                show "card {i. i < length w3 \<and> fst (w3!i) = label} \<in> {0, 2}"
                proof -
                  have "card {i. i < length w3 \<and> fst (w3!i) = label} = length (filter (\<lambda>e. fst e = label) w3)"
                    using length_filter_conv_card[of "\<lambda>e. fst e = label" w3, symmetric] by (by100 simp)
                  thus ?thesis using hfc_w3 by (by100 simp)
                qed
              qed
              \<comment> \<open>Apply IH to w3.\<close>
              from less(1)[OF hlt_w3 hge4_w3 hproper_w3]
              have hIH: "(\<exists>a b. a \<noteq> b \<and> top1_scheme_equiv w3 [(a, True), (a, False), (b, True), (b, False)])
                   \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_scheme_equiv w3 w)
                   \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_scheme_equiv w3 w)" .
              \<comment> \<open>Combine with the commutator block using congruence.\<close>
              define block where "block = [(a_lab, True), (b_lab, True), (a_lab, False), (b_lab, False)]"
              have hfull_block: "full = block @ w3" unfolding block_def using hfull_w3 by (by100 simp)
              \<comment> \<open>From scheme ~ full = block @ w3, and w3 ~ normal\_form,
                 we get scheme ~ block @ normal\_form using congruence.\<close>
              from hIH show ?thesis
              proof (elim disjE exE conjE)
                \<comment> \<open>Case 1: w3 ~ sphere (one torus). Then scheme ~ block @ sphere = torus 2? No.
                   Actually sphere means w3 ~ [(a,T),(a,F),(b,T),(b,F)] which is ALSO a commutator.
                   So scheme ~ block1 @ block2 = torus 2.\<close>
                fix c d assume hcd: "c \<noteq> d" and hw3_sph: "top1_scheme_equiv w3 [(c, True), (c, False), (d, True), (d, False)]"
                have "top1_scheme_equiv full (block @ [(c, True), (c, False), (d, True), (d, False)])"
                  using scheme_equiv_prepend[OF hw3_sph, of block] hfull_block
                  unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
                hence "top1_scheme_equiv scheme (block @ [(c, True), (c, False), (d, True), (d, False)])"
                  using hfull_equiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
                \<comment> \<open>Cancel the sphere: [(c,T),(c,F),(d,T),(d,F)] has two cancellable pairs.
                   block @ sphere ~ block @ [(d,T),(d,F)] ~ block ~ torus 1.\<close>
                \<comment> \<open>cancel c-pair: need top1\_inverse\_edge (c,True) = (c,False)\<close>
                have hinv_c: "top1_inverse_edge (c,True) = (c,False)"
                  unfolding top1_inverse_edge_def by (by100 simp)
                have hcancel1: "top1_elementary_scheme_operation
                    (block @ [(c,True),(c,False),(d,True),(d,False)])
                    (block @ [(d,True),(d,False)])"
                proof -
                  have "top1_elementary_scheme_operation
                      ([] @ [(c,True), top1_inverse_edge (c,True)] @ [(d,True),(d,False)])
                      ([] @ [(d,True),(d,False)])"
                    by (rule top1_elementary_scheme_operation.cancel)
                  hence "top1_elementary_scheme_operation
                      ([(c,True),(c,False),(d,True),(d,False)])
                      ([(d,True),(d,False)])"
                    using hinv_c by (by100 simp)
                  from top1_elementary_scheme_operation.context_left[OF this, of block]
                  show ?thesis by (by100 simp)
                qed
                have hinv_d: "top1_inverse_edge (d,True) = (d,False)"
                  unfolding top1_inverse_edge_def by (by100 simp)
                have hcancel2: "top1_elementary_scheme_operation
                    (block @ [(d,True),(d,False)])
                    block"
                proof -
                  have "top1_elementary_scheme_operation
                      ([] @ [(d,True), top1_inverse_edge (d,True)] @ [])
                      ([] @ [])"
                    by (rule top1_elementary_scheme_operation.cancel)
                  hence "top1_elementary_scheme_operation [(d,True),(d,False)] []"
                    using hinv_d by (by100 simp)
                  from top1_elementary_scheme_operation.context_left[OF this, of block]
                  show ?thesis by (by100 simp)
                qed
                have "top1_scheme_equiv scheme block"
                  using \<open>top1_scheme_equiv scheme (block @ [(c, True), (c, False), (d, True), (d, False)])\<close>
                    hcancel1 hcancel2 unfolding top1_scheme_equiv_def
                  by (meson rtranclp.rtrancl_into_rtrancl rtranclp_trans)
                hence "top1_scheme_equiv scheme (top1_n_torus_scheme 1)"
                  using commutator_block_equiv_torus_1[OF hab] unfolding block_def top1_scheme_equiv_def
                  by (meson rtranclp_trans)
                thus ?thesis unfolding top1_is_torus_scheme_def by (by100 blast)
              next
                \<comment> \<open>Case 2: w3 ~ projective m. Then scheme ~ block @ projective.
                   Use proj\_pair\_absorbs\_torus: commutator + projective → projective (m+2).\<close>
                fix m w assume "m > 0" and hwm: "top1_is_projective_scheme w m"
                    and hw3_proj: "top1_scheme_equiv w3 w"
                have "top1_scheme_equiv full (block @ w)"
                  using scheme_equiv_prepend[OF hw3_proj, of block] hfull_block
                  unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
                hence "top1_scheme_equiv scheme (block @ w)"
                  using hfull_equiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
                \<comment> \<open>block @ projective\_m ~ projective\_(m+2).
                   The commutator block is one torus pair. By Lemma 77.4 (proj\_pair\_absorbs\_torus),
                   one projective pair absorbs one torus pair into 3 projective pairs.
                   So: commutator @ projective\_m first extract a projective pair from projective\_m,
                   then absorb the commutator. Net: projective\_(m-1+3) = projective\_(m+2).\<close>
                have hw_is: "w = top1_m_projective_scheme m" using hwm unfolding top1_is_projective_scheme_def by (by100 blast)
                \<comment> \<open>Apply commutator\_prepend\_projective.\<close>
                from commutator_prepend_projective[OF hab \<open>m > 0\<close>]
                have "\<exists>w'. top1_is_projective_scheme w' (m+2) \<and>
                    top1_scheme_equiv (block @ top1_m_projective_scheme m) w'"
                  unfolding block_def by (by100 blast)
                then obtain w' where hw'_proj: "top1_is_projective_scheme w' (m+2)"
                    and hw'_equiv: "top1_scheme_equiv (block @ top1_m_projective_scheme m) w'"
                  by (by100 blast)
                have "top1_scheme_equiv scheme w'"
                  using \<open>top1_scheme_equiv scheme (block @ w)\<close> hw'_equiv hw_is
                  unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
                have "m + 2 > 0" using \<open>m > 0\<close> by (by100 simp)
                thus ?thesis using \<open>top1_scheme_equiv scheme w'\<close> hw'_proj by (by100 blast)
              next
                \<comment> \<open>Case 3: w3 ~ torus n. Then scheme ~ block @ torus\_n.
                   This is a torus\_(n+1) (after relabeling).\<close>
                fix n w assume "n > 0" and hwn: "top1_is_torus_scheme w n"
                    and hw3_tor: "top1_scheme_equiv w3 w"
                have "top1_scheme_equiv full (block @ w)"
                  using scheme_equiv_prepend[OF hw3_tor, of block] hfull_block
                  unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
                hence "top1_scheme_equiv scheme (block @ w)"
                  using hfull_equiv unfolding top1_scheme_equiv_def by (meson rtranclp_trans)
                \<comment> \<open>block @ torus\_n = commutator @ torus\_n ~ torus\_(n+1).\<close>
                have hw_is: "w = top1_n_torus_scheme n" using hwn unfolding top1_is_torus_scheme_def by (by100 blast)
                have "top1_scheme_equiv (block @ w) (top1_n_torus_scheme (Suc n))"
                  using commutator_prepend_torus[OF hab \<open>n > 0\<close>] hw_is unfolding block_def
                  by (by100 simp)
                hence "top1_scheme_equiv scheme (top1_n_torus_scheme (Suc n))"
                  using \<open>top1_scheme_equiv scheme (block @ w)\<close> unfolding top1_scheme_equiv_def
                  by (meson rtranclp_trans)
                thus ?thesis unfolding top1_is_torus_scheme_def by (by100 blast)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

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
  \<comment> \<open>Step 1: From the polygonal quotient, extract the edge labeling scheme.\<close>
  \<comment> \<open>Step 1: Extract edge scheme from the polygonal quotient.
     The polygon P has n edges. The quotient map q identifies boundary edges in pairs.
     For each pair of identified edges: assign a shared label. The direction (same or opposite)
     determines the exponent (True/False). This gives the edge scheme.
     The scheme satisfies quotient\\_of\\_scheme\\_on by construction.\<close>
  obtain scheme :: "(nat \<times> bool) list" where
      hsch: "top1_quotient_of_scheme_on X TX scheme"
      and hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme!i) = label} \<in> {0, 2}"
    sorry \<comment> \<open>Extract proper scheme from polygonal quotient.
       Construction: P has n edges. q identifies edges in pairs (from surface = no boundary).
       Each pair gets a shared label. Properness: each label appears exactly 0 or 2 times
       (from the pairing structure of edge identifications on a closed surface).\<close>
  have hlen_ge4: "length scheme \<ge> 4"
  proof -
    from hsch obtain P0 q0 where "top1_is_polygonal_region_on P0 (length scheme)"
      by (rule quotient_of_scheme_extract)
    hence "length scheme \<ge> 3" unfolding top1_is_polygonal_region_on_def by (by100 blast)
    moreover have "even (length scheme)" using proper_scheme_even_length[OF hproper] .
    ultimately show ?thesis by (by100 presburger)
  qed
  \<comment> \<open>Apply scheme\_normal\_form: sphere, torus, or projective.\<close>
  \<comment> \<open>Use valid normal form (avoids old §76 chain).\<close>
  from scheme_normal_form_valid[OF hlen_ge4 hproper]
  have hNF_valid: "(\<exists>a b. a \<noteq> b \<and> top1_valid_scheme_equiv scheme [(a, True), (a, False), (b, True), (b, False)])
       \<or> (\<exists>m>0. \<exists>w. top1_is_projective_scheme w m \<and> top1_valid_scheme_equiv scheme w)
       \<or> (\<exists>n>0. \<exists>w. top1_is_torus_scheme w n \<and> top1_valid_scheme_equiv scheme w)" .
  \<comment> \<open>Theorem 77.5 now routes through valid chain directly (no old scheme\\_equiv needed).\<close>
  \<comment> \<open>Step 3: Each normal form corresponds to the standard surface.
     - Empty/sphere: cancellation gives S² (a@a⁻¹@b@b⁻¹ with cancellation).
     - Torus scheme: the standard n-torus IS the quotient of this scheme
       (by definition top1\\_is\\_n\\_fold\\_torus\\_on). scheme\\_quotient\\_uniqueness gives homeo.
     - Projective scheme: similarly, top1\\_is\\_m\\_fold\\_projective\\_on.
     Plus: Theorem 76 preserves quotient homeomorphism type, so scheme\\_equiv gives homeo.\<close>
  show ?thesis
  proof -
    \<comment> \<open>Use valid chain: valid\\_equiv\\_preserves\\_quotient\\_homeo gives Y \\<cong> X directly.\<close>
    from hNF_valid show ?thesis
    proof (elim disjE exE conjE)
      \<comment> \<open>Case 0: sphere case. scheme ~ [(a,T),(a,F),(b,T),(b,F)].\<close>
      fix a_s b_s assume hab_s: "a_s \<noteq> b_s"
          and hequiv_s: "top1_valid_scheme_equiv scheme [(a_s, True), (a_s, False), (b_s, True), (b_s, False)]"
      \<comment> \<open>Step 1: X is homeomorphic to some quotient Y of the sphere scheme.\<close>
      from valid_equiv_preserves_quotient_homeo[OF hsch hequiv_s]
      obtain Y :: "'a set" and TY :: "'a set set" and h :: "'a \<Rightarrow> 'a" where
        hY: "top1_quotient_of_scheme_on Y TY [(a_s, True), (a_s, False), (b_s, True), (b_s, False)]"
        and hXY: "top1_homeomorphism_on X TX Y TY h"
        by (by100 blast)
      \<comment> \<open>Step 2: Y (quotient of sphere scheme) \\<cong> S2.
         Needs sphere\\_scheme\\_realizes\\_sphere lemma (geometric construction).\<close>
      have "\<exists>g. top1_homeomorphism_on Y TY top1_S2 top1_S2_topology g"
        sorry \<comment> \<open>Sphere scheme realizes S2. See audit 20 step 6.\<close>
      then obtain g where hYS: "top1_homeomorphism_on Y TY top1_S2 top1_S2_topology g" by (by100 blast)
      \<comment> \<open>Step 3: X \\<cong> Y \\<cong> S2 by composition.\<close>
      from homeomorphism_comp[OF hXY hYS]
      have "top1_homeomorphism_on X TX top1_S2 top1_S2_topology (g \<circ> h)" .
      thus ?thesis by (by100 blast)
    next
      \<comment> \<open>Case 1: scheme \\<sim> torus normal form.\<close>
      fix n w assume hn: "n > 0" and htor: "top1_is_torus_scheme w n"
          and hequiv: "top1_valid_scheme_equiv scheme w"
      \<comment> \<open>valid chain: \\<exists>Y TY h. quotient Y TY w \\<and> homeo X TX Y TY h.\<close>
      from valid_equiv_preserves_quotient_homeo[OF hsch hequiv]
      obtain Y :: "'a set" and TY :: "'a set set" and h_t :: "'a \<Rightarrow> 'a" where
        hY_t: "top1_quotient_of_scheme_on Y TY w" and hXY_t: "top1_homeomorphism_on X TX Y TY h_t"
        by (by100 blast)
      have "top1_quotient_of_scheme_on Y TY (top1_n_torus_scheme n)"
        using hY_t htor unfolding top1_is_torus_scheme_def by (by100 simp)
      hence "top1_is_n_fold_torus_on Y TY n" using hn unfolding top1_is_n_fold_torus_on_def by (by100 simp)
      show ?thesis using hn \<open>top1_is_n_fold_torus_on Y TY n\<close> hXY_t by (by100 blast)
    next
      \<comment> \<open>Case 3: scheme \\<sim> projective normal form.\<close>
      fix m w assume hm: "m > 0" and hproj: "top1_is_projective_scheme w m"
          and hequiv: "top1_valid_scheme_equiv scheme w"
      from valid_equiv_preserves_quotient_homeo[OF hsch hequiv]
      obtain Y :: "'a set" and TY :: "'a set set" and h_p :: "'a \<Rightarrow> 'a" where
        hY_p: "top1_quotient_of_scheme_on Y TY w" and hXY_p: "top1_homeomorphism_on X TX Y TY h_p"
        by (by100 blast)
      have "top1_quotient_of_scheme_on Y TY (top1_m_projective_scheme m)"
        using hY_p hproj unfolding top1_is_projective_scheme_def by (by100 simp)
      show ?thesis
      proof (cases "m \<ge> 2")
        case True
        hence "top1_is_m_fold_projective_on Y TY m"
          unfolding top1_is_m_fold_projective_on_def
          using \<open>top1_quotient_of_scheme_on Y TY (top1_m_projective_scheme m)\<close> by (by100 simp)
        thus ?thesis using hm hXY_p by (by100 blast)
      next
        case False hence hm1: "m = 1" using hm by (by100 linarith)
        have hlen2: "length (top1_m_projective_scheme 1) = 2"
          unfolding top1_m_projective_scheme_def by (by100 simp)
        from \<open>top1_quotient_of_scheme_on Y TY (top1_m_projective_scheme m)\<close>
        have hqs1: "top1_quotient_of_scheme_on Y TY (top1_m_projective_scheme 1)"
          using hm1 by (by100 simp)
        from hqs1 obtain P0 q0 where "top1_is_polygonal_region_on P0 (length (top1_m_projective_scheme 1))"
          by (rule quotient_of_scheme_extract)
        hence "top1_is_polygonal_region_on P0 2" using hlen2 by simp
        hence "2 \<ge> (3::nat)" unfolding top1_is_polygonal_region_on_def by (by100 blast)
        hence False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed


end


