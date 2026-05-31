theory AlgTopCached9
  imports "AlgTopCached8.AlgTopCached8"
begin

(* Cached sorry-free: free_group_hom_subset_injective + Theorem 71.3 (infinite case). *)

\<comment> \<open>Free group embedding: a group hom from free(S1) to free(S2) that maps generators
   to generators is injective, when S1 \\<subseteq> S2.\<close>
lemma free_group_hom_subset_injective:
  fixes S1 :: "'s set" and S2 :: "'s set"
  assumes hfree1: "top1_is_free_group_full_on G1 mul1 e1 invg1 \<iota>1 S1"
      and hfree2: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<iota>2 S2"
      and hS12: "S1 \<subseteq> S2"
      and hhom: "top1_group_hom_on G1 mul1 G2 mul2 \<phi>"
      and hgen_map: "\<forall>s\<in>S1. \<phi> (\<iota>1 s) = \<iota>2 s"
  shows "inj_on \<phi> G1"
proof (rule inj_onI)
  fix x y assume hx: "x \<in> G1" and hy: "y \<in> G1" and heq: "\<phi> x = \<phi> y"
  have hG1: "top1_is_group_on G1 mul1 e1 invg1"
    using hfree1 unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG2: "top1_is_group_on G2 mul2 e2 invg2"
    using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>\\<phi>(x * y\<inverse>) = \\<phi>(x) * \\<phi>(y)\<inverse> = e2. So x * y\<inverse> \\<in> ker(\\<phi>).
     Need: ker(\\<phi>) = {e1}. Sufficient: \\<phi>(z) = e2 \\<Longrightarrow> z = e1.\<close>
  have hxy_inv: "mul1 x (invg1 y) \<in> G1"
    using hG1 hx hy unfolding top1_is_group_on_def by (by100 blast)
  have hphi_xy: "\<phi> (mul1 x (invg1 y)) = e2"
  proof -
    have hinvy: "invg1 y \<in> G1" using hG1 hy unfolding top1_is_group_on_def by (by100 blast)
    have "\<phi> (mul1 x (invg1 y)) = mul2 (\<phi> x) (\<phi> (invg1 y))"
      using hhom hx hinvy unfolding top1_group_hom_on_def by (by100 blast)
    also have "\<phi> (invg1 y) = invg2 (\<phi> y)"
      using hom_preserves_inv[OF hG1 hG2 hhom hy] by (by100 simp)
    also have "mul2 (\<phi> x) (invg2 (\<phi> y)) = mul2 (\<phi> y) (invg2 (\<phi> y))"
      using heq by (by100 simp)
    also have "... = e2" using hG2 hhom hy
      unfolding top1_is_group_on_def top1_group_hom_on_def by (by100 blast)
    finally show ?thesis .
  qed
  \<comment> \<open>Show: z = mul1 x (invg1 y) = e1. Then x = y.\<close>
  have "mul1 x (invg1 y) = e1"
  proof -
    let ?z = "mul1 x (invg1 y)"
    \<comment> \<open>?z \\<in> G1 = subgroup\\_generated(\\<iota>1 ` S1). By word\\_repr, ?z = e1 or has a word.\<close>
    have "\<iota>1 ` S1 \<subseteq> G1"
      using hfree1 unfolding top1_is_free_group_full_on_def by (by100 blast)
    have hG1_gen: "G1 = top1_subgroup_generated_on G1 mul1 e1 invg1 (\<iota>1 ` S1)"
      using hfree1 unfolding top1_is_free_group_full_on_def by (by100 blast)
    have "?z \<in> top1_subgroup_generated_on G1 mul1 e1 invg1 (\<iota>1 ` S1)"
      using hxy_inv hG1_gen by (by100 simp)
    from subgroup_generated_word_repr[OF hG1 \<open>\<iota>1 ` S1 \<subseteq> G1\<close> this]
    have "?z = e1 \<or> (\<exists>ws. length ws > 0 \<and>
        (\<forall>i<length ws. ws ! i \<in> \<iota>1 ` S1 \<or> (\<exists>s\<in>\<iota>1 ` S1. ws ! i = invg1 s)) \<and>
        foldr mul1 ws e1 = ?z)" .
    thus "?z = e1"
    proof
      assume "?z = e1" thus ?thesis .
    next
      assume "\<exists>ws. length ws > 0 \<and>
          (\<forall>i<length ws. ws ! i \<in> \<iota>1 ` S1 \<or> (\<exists>s\<in>\<iota>1 ` S1. ws ! i = invg1 s)) \<and>
          foldr mul1 ws e1 = ?z"
      then obtain ws where hws_len: "length ws > 0"
          and hws_in: "\<forall>i<length ws. ws ! i \<in> \<iota>1 ` S1 \<or> (\<exists>s\<in>\<iota>1 ` S1. ws ! i = invg1 s)"
          and hws_eq: "foldr mul1 ws e1 = ?z" by (by100 blast)
      \<comment> \<open>Convert ws to an (s, bool) list sb.\<close>
      \<comment> \<open>Each ws!i is either \\<iota>1(s) (True) or invg1(\\<iota>1(s)) (False) for some s \\<in> S1.\<close>
      \<comment> \<open>Then word\\_product(G1, map (%(s,b). (\\<iota>1 s, b)) sb) = foldr mul1 ws e1 = ?z.\<close>
      \<comment> \<open>\\<phi>(?z) = e2. By hom\\_word\\_product: word\\_product(G2, map (%(s,b). (\\<phi>(\\<iota>1 s), b)) sb) = e2.\<close>
      \<comment> \<open>\\<phi>(\\<iota>1 s) = \\<iota>2 s. So word\\_product(G2, map (%(s,b). (\\<iota>2 s, b)) sb) = e2.\<close>
      \<comment> \<open>Apply free\\_group\\_word\\_kernel to free(S2) = G2 with target G1 and map
         \\<phi>2(s) = \\<iota>1(s) for s \\<in> S1, \\<phi>2(s) = e1 for s \\<notin> S1:
         word\\_product(G1, map (%(s,b). (\\<phi>2 s, b)) sb) = e1.
         Since all s in sb are in S1: \\<phi>2(s) = \\<iota>1(s).
         So word\\_product(G1, map (%(s,b). (\\<iota>1 s, b)) sb) = e1 = ?z.
         But ?z = foldr mul1 ws e1 \\<noteq> e1 (by the assumption we're in the \\<exists> branch).

         Wait -- ?z \\<noteq> e1 only if we assumed that. Let me check: we're in the
         \\<exists>ws branch of the disjunction, which means ws is non-empty.
         But word\\_product = ?z and word\\_product via \\<phi>2 = e1.
         So ?z = e1 after all. This means the \\<exists>ws branch gives ?z = e1 too!\<close>
      \<comment> \<open>Convert ws to (s, bool) list.\<close>
      have "\<forall>i<length ws. \<exists>s\<in>S1. ws ! i = \<iota>1 s \<or> ws ! i = invg1 (\<iota>1 s)"
      proof (intro allI impI)
        fix i assume "i < length ws"
        from hws_in[rule_format, OF this]
        show "\<exists>s\<in>S1. ws ! i = \<iota>1 s \<or> ws ! i = invg1 (\<iota>1 s)"
          by (by100 blast)
      qed
      \<comment> \<open>By choice, obtain a function picking s for each position.\<close>
      hence "\<exists>sf. \<forall>i<length ws. sf i \<in> S1 \<and> (ws ! i = \<iota>1 (sf i) \<or> ws ! i = invg1 (\<iota>1 (sf i)))"
        by (by5000 metis)
      then obtain sf where hsf: "\<forall>i<length ws. sf i \<in> S1 \<and>
          (ws ! i = \<iota>1 (sf i) \<or> ws ! i = invg1 (\<iota>1 (sf i)))" by (by100 blast)
      \<comment> \<open>Define the boolean: True if ws!i = \\<iota>1(sf i), False if invg1.\<close>
      define bf where "bf i = (ws ! i = \<iota>1 (sf i))" for i
      define sb where "sb = map (\<lambda>i. (sf i, bf i)) [0..<length ws]"
      \<comment> \<open>word\\_product(G1, map (%s. (\\<iota>1 s, b)) sb) = foldr mul1 ws e1 = ?z.\<close>
      have hwp_eq: "top1_group_word_product mul1 e1 invg1
          (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) = ?z"
      proof -
        \<comment> \<open>By word\\_product\\_as\\_foldr, word\\_product = foldr mul1 (mapped list) e1.
           The mapped list equals ws, so the result equals foldr mul1 ws e1 = ?z.\<close>
        have "top1_group_word_product mul1 e1 invg1 (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) =
            foldr mul1 (map (\<lambda>(x,b). if b then x else invg1 x)
                (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) e1"
          by (rule word_product_as_foldr)
        \<comment> \<open>Show: map ... (map ... sb) = ws.\<close>
        moreover have "map (\<lambda>(x,b). if b then x else invg1 x)
            (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) = ws"
        proof (rule nth_equalityI)
          show "length (map (\<lambda>(x,b). if b then x else invg1 x)
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) = length ws"
            unfolding sb_def by (by100 simp)
        next
          fix i assume "i < length (map (\<lambda>(x,b). if b then x else invg1 x)
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb))"
          hence hi: "i < length ws" unfolding sb_def by (by100 simp)
          \<comment> \<open>The i-th element of the composed map is:
             if bf i then \\<iota>1(sf i) else invg1(\\<iota>1(sf i)).
             By bf\\_def, this equals ws!i in both cases.\<close>
          have "sb ! i = (sf i, bf i)" unfolding sb_def using hi by (by100 simp)
          hence "(\<lambda>(s,b). (\<iota>1 s, b)) (sb ! i) = (\<iota>1 (sf i), bf i)"
            by (by100 simp)
          hence "(map (\<lambda>(s,b). (\<iota>1 s, b)) sb) ! i = (\<iota>1 (sf i), bf i)"
            unfolding sb_def using hi by (by100 simp)
          hence "(map (\<lambda>(x,b). if b then x else invg1 x)
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) ! i =
              (if bf i then \<iota>1 (sf i) else invg1 (\<iota>1 (sf i)))"
            unfolding sb_def using hi by (by100 simp)
          also have "... = ws ! i"
          proof (cases "bf i")
            case True
            hence "ws ! i = \<iota>1 (sf i)" unfolding bf_def by (by100 simp)
            thus ?thesis using True by (by100 simp)
          next
            case False
            hence "ws ! i \<noteq> \<iota>1 (sf i)" unfolding bf_def by (by100 simp)
            from hsf[rule_format, OF hi] this
            have "ws ! i = invg1 (\<iota>1 (sf i))" by (by100 blast)
            thus ?thesis using False by (by100 simp)
          qed
          finally show "(map (\<lambda>(x,b). if b then x else invg1 x)
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) ! i = ws ! i" .
        qed
        ultimately show ?thesis using hws_eq by (by100 simp)
      qed
      \<comment> \<open>All generators in S1.\<close>
      have hsb_in: "\<forall>i<length sb. fst (sb ! i) \<in> S1"
        unfolding sb_def using hsf by (by100 auto)
      \<comment> \<open>\\<phi>(?z) = e2. So \\<phi>(word\\_product(G1, ...)) = e2.\<close>
      \<comment> \<open>By hom\\_word\\_product: word\\_product(G2, \\<phi>-mapped) = e2.\<close>
      \<comment> \<open>\\<phi>(\\<iota>1 s) = \\<iota>2 s for s \\<in> S1.\<close>
      \<comment> \<open>Apply free\\_group\\_word\\_kernel to G2 = free(S2) with target G1
         and map \\<phi>2(s) = \\<iota>1 s for s \\<in> S1, e1 otherwise:
         word\\_product(G1, ...) = e1.\<close>
      have "top1_group_word_product mul1 e1 invg1
          (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) = e1"
      proof -
        \<comment> \<open>\\<phi>(word\\_product(G1, sb)) = word\\_product(G2, \\<phi>-sb) = e2.\<close>
        have hsb_in_G1: "\<forall>i<length (map (\<lambda>(s,b). (\<iota>1 s, b)) sb).
            fst ((map (\<lambda>(s,b). (\<iota>1 s, b)) sb) ! i) \<in> G1"
        proof (intro allI impI)
          fix i assume "i < length (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)"
          hence "i < length sb" by (by100 simp)
          hence "fst (sb ! i) \<in> S1" using hsb_in by (by100 blast)
          hence "\<iota>1 (fst (sb ! i)) \<in> G1" using \<open>\<iota>1 ` S1 \<subseteq> G1\<close> by (by100 blast)
          obtain s' b' where "sb ! i = (s', b')" by (cases "sb ! i") (by100 blast)
          thus "fst ((map (\<lambda>(s,b). (\<iota>1 s, b)) sb) ! i) \<in> G1"
            using \<open>i < length sb\<close> \<open>\<iota>1 (fst (sb ! i)) \<in> G1\<close> \<open>sb ! i = (s', b')\<close> by (by100 simp)
        qed
        have hphi_wp: "\<phi> (top1_group_word_product mul1 e1 invg1
            (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) = e2"
          using hwp_eq hphi_xy by (by100 simp)
        \<comment> \<open>word\\_product(G2, [(\\<iota>2 s, b)]) = e2 (by hom\\_word\\_product + hgen\\_map).\<close>
        have hphi_mapped: "top1_group_word_product mul2 e2 invg2
            (map (\<lambda>(s,b). (\<iota>2 s, b)) sb) = e2"
        proof -
          from hom_word_product[OF hG1 hG2 hhom hsb_in_G1]
          have "\<phi> (top1_group_word_product mul1 e1 invg1
              (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) =
              top1_group_word_product mul2 e2 invg2
              (map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb))" .
          moreover have "map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) =
              map (\<lambda>(s,b). (\<iota>2 s, b)) sb"
          proof (rule nth_equalityI)
            show "length (map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) =
                length (map (\<lambda>(s,b). (\<iota>2 s, b)) sb)" by (by100 simp)
          next
            fix i assume "i < length (map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb))"
            hence hi: "i < length sb" by (by100 simp)
            have "fst (sb ! i) \<in> S1" using hsb_in hi by (by100 blast)
            hence "\<phi> (\<iota>1 (fst (sb ! i))) = \<iota>2 (fst (sb ! i))"
              using hgen_map by (by100 blast)
            obtain s' b' where "sb ! i = (s', b')" by (cases "sb ! i") (by100 blast)
            thus "(map (\<lambda>(x,b). (\<phi> x, b)) (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)) ! i =
                (map (\<lambda>(s,b). (\<iota>2 s, b)) sb) ! i"
              using hi \<open>\<phi> (\<iota>1 (fst (sb ! i))) = \<iota>2 (fst (sb ! i))\<close> \<open>sb ! i = (s', b')\<close>
              by (by100 simp)
          qed
          ultimately show ?thesis using hphi_wp by (by5000 metis)
        qed
        \<comment> \<open>Apply free\\_group\\_word\\_kernel to G2 with target G1.\<close>
        have hsb_in_S2: "\<forall>i<length sb. fst (sb ! i) \<in> S2"
          using hsb_in hS12 by (by100 blast)
        define \<phi>2 where "\<phi>2 s = (if s \<in> S1 then \<iota>1 s else e1)" for s
        have h\<phi>2_in: "\<forall>s\<in>S2. \<phi>2 s \<in> G1"
        proof (intro ballI)
          fix s assume "s \<in> S2"
          show "\<phi>2 s \<in> G1"
          proof (cases "s \<in> S1")
            case True
            hence "\<phi>2 s = \<iota>1 s" unfolding \<phi>2_def by (by100 simp)
            thus ?thesis using \<open>\<iota>1 ` S1 \<subseteq> G1\<close> True by (by100 blast)
          next
            case False
            hence "\<phi>2 s = e1" unfolding \<phi>2_def by (by100 simp)
            thus ?thesis using hG1 unfolding top1_is_group_on_def by (by100 blast)
          qed
        qed
        from free_group_word_kernel[OF hfree2 hG1 h\<phi>2_in hsb_in_S2 hphi_mapped]
        have "top1_group_word_product mul1 e1 invg1
            (map (\<lambda>(s,b). (\<phi>2 s, b)) sb) = e1" .
        \<comment> \<open>Since all s in sb are in S1: \\<phi>2 s = \\<iota>1 s.\<close>
        moreover have "map (\<lambda>(s,b). (\<phi>2 s, b)) sb = map (\<lambda>(s,b). (\<iota>1 s, b)) sb"
        proof (rule nth_equalityI)
          show "length (map (\<lambda>(s,b). (\<phi>2 s, b)) sb) = length (map (\<lambda>(s,b). (\<iota>1 s, b)) sb)"
            by (by100 simp)
        next
          fix i assume "i < length (map (\<lambda>(s,b). (\<phi>2 s, b)) sb)"
          hence "i < length sb" by (by100 simp)
          hence "fst (sb ! i) \<in> S1" using hsb_in by (by100 blast)
          hence "\<phi>2 (fst (sb ! i)) = \<iota>1 (fst (sb ! i))" unfolding \<phi>2_def by (by100 simp)
          obtain si bi where "sb ! i = (si, bi)" by (cases "sb ! i") (by100 blast)
          hence "(\<lambda>(s,b). (\<phi>2 s, b)) (sb ! i) = (\<phi>2 si, bi)" by (by100 simp)
          also have "... = (\<iota>1 si, bi)" using \<open>\<phi>2 (fst (sb ! i)) = \<iota>1 (fst (sb ! i))\<close>
            \<open>sb ! i = (si, bi)\<close> by (by100 simp)
          also have "... = (\<lambda>(s,b). (\<iota>1 s, b)) (sb ! i)" using \<open>sb ! i = (si, bi)\<close> by (by100 simp)
          finally show "(map (\<lambda>(s,b). (\<phi>2 s, b)) sb) ! i = (map (\<lambda>(s,b). (\<iota>1 s, b)) sb) ! i"
            using \<open>i < length sb\<close> by (by100 simp)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>So ?z = e1.\<close>
      show "?z = e1" using hwp_eq \<open>top1_group_word_product mul1 e1 invg1 _ = e1\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>mul1 x (invg1 y) = e1 implies x = y.\<close>
  thus "x = y" using hG1 hx hy
    unfolding top1_is_group_on_def by (by5000 metis)
qed

\<comment> \<open>Theorem\_71\_3\_finite moved to AlgTopCached8.\<close>


\<comment> \<open>Theorem 71.3 (book-faithful): \\<pi>\\_1(X, p) is free with generators indexed by J.
   This is the actual book statement — \\<pi>\\_1 itself is the free group.\<close>
theorem Theorem_71_3_pi1_free:
  fixes J :: "'i set" and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX J p"
  shows "\<exists>(\<iota>::'i \<Rightarrow> _). top1_is_free_group_full_on
      (top1_fundamental_group_carrier X TX p)
      (top1_fundamental_group_mul X TX p)
      (top1_fundamental_group_id X TX p)
      (top1_fundamental_group_invg X TX p)
      \<iota> J"
proof -
  \<comment> \<open>Extract circles from wedge definition.\<close>
  from assms[unfolded top1_is_wedge_of_circles_on_def]
  obtain C where
    hstrict: "is_topology_on_strict X TX" and hhaus: "is_hausdorff_on X TX" and hp: "p \<in> X"
    and hC: "\<forall>\<alpha>\<in>J. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
           \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h)"
    and hcover: "(\<Union>\<alpha>\<in>J. C \<alpha>) = X"
    and hdisjoint: "\<forall>\<alpha>\<in>J. \<forall>\<beta>\<in>J. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
    and hweak: "\<forall>D. D \<subseteq> X \<longrightarrow>
           (closedin_on X TX D \<longleftrightarrow>
            (\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
    by (elim conjE exE) (rule that, assumption+)
  have hTX: "is_topology_on X TX" using hstrict unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>For each \\<alpha>, choose a generator loop f\\_\\<alpha> in C\\_\\<alpha>.\<close>
  \<comment> \<open>Define \\<iota>(\\<alpha>) = [f\\_\\<alpha>] \\<in> \\<pi>\\_1(X, p).\<close>
  \<comment> \<open>The book proves three things:
     (1) The groups G\\_\\<alpha> = image of \\<pi>\\_1(C\\_\\<alpha>) generate \\<pi>\\_1(X).
     (2) The inclusions i\\_\\<alpha> are monomorphisms.
     (3) No reduced word in the G\\_\\<alpha> equals the identity.
     All three use the fact that loops/homotopies lie in finite sub-wedges.\<close>
  \<comment> \<open>This is a complex proof requiring the full infrastructure from above
     (hC\\_open, hcompact\\_finite, hloop\\_finite) plus hhtpy\\_finite and hfinite\\_free.
     We defer to a detailed sorry-first skeleton.\<close>
  show ?thesis
  proof (cases "finite J")
    case True
    \<comment> \<open>Finite case: from Theorem\\_71\\_3\\_finite.\<close>
    from Theorem_71_3_finite[OF assms True]
    obtain G :: "int set" and mul e invg and \<iota> :: "'i \<Rightarrow> int" where
      hfree: "top1_is_free_group_full_on G mul e invg \<iota> J" and
      hiso: "top1_groups_isomorphic_on G mul
          (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)"
      by (by100 blast)
    \<comment> \<open>Transfer freeness from G to \\<pi>\\_1 via the isomorphism.\<close>
    have hpi1_grp: "top1_is_group_on
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
        (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)"
      by (rule top1_fundamental_group_is_group[OF hTX hp])
    from free_group_iso_transfer[OF hfree hiso hpi1_grp]
    show ?thesis by (by100 blast)
  next
    case False
    \<comment> \<open>Infinite case: book proof using compactness + coherent topology.
       Every loop/homotopy lies in a finite sub-wedge (hloop\\_finite, hhtpy\\_finite).
       Each finite sub-wedge has free \\<pi>\\_1 (Theorem 71.1).
       The three conditions of top1\\_is\\_free\\_group\\_full\\_on each reduce to the finite case:
       (1) Generators generate: loop in finite sub-wedge \\<Rightarrow> product of generators.
       (2) Injectivity: loop in C\\_\\<beta> homotopic to constant in X \\<Rightarrow> in finite sub-wedge \\<Rightarrow> in C\\_\\<beta>.
       (3) No reduced word = id: word in finite sub-wedge \\<Rightarrow> contradicts Theorem 71.1.\<close>
    \<comment> \<open>Inline the infrastructure from the general theorem's infinite case.\<close>
    \<comment> \<open>C\\_\\<alpha> - {p} open, compact meets finitely many, loop in finite sub-wedge.\<close>
    have hC_open: "\<And>\<alpha>. \<alpha> \<in> J \<Longrightarrow> C \<alpha> - {p} \<in> TX"
    proof -
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
      \<comment> \<open>Show X - (C\\_\\<alpha> - {p}) is closed, i.e. for each \\<beta>, C\\_\\<beta> \\<inter> (X - (C\\_\\<alpha> - {p})) closed in C\\_\\<beta>.\<close>
      have hcl: "closedin_on X TX (X - (C \<alpha> - {p}))"
      proof -
        have hsub: "X - (C \<alpha> - {p}) \<subseteq> X" by (by100 blast)
        have "\<forall>\<beta>\<in>J. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> (X - (C \<alpha> - {p})))"
        proof (intro ballI)
          fix \<beta> assume h\<beta>: "\<beta> \<in> J"
          show "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> (X - (C \<alpha> - {p})))"
          proof (cases "\<beta> = \<alpha>")
            case True
            hence "C \<beta> \<inter> (X - (C \<alpha> - {p})) = {p}"
              using hC h\<alpha> by (by100 blast)
            moreover have "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) {p}"
            proof -
              have "C \<beta> \<subseteq> X" using hC h\<beta> by (by100 blast)
              have "p \<in> C \<beta>" using hC h\<beta> by (by100 blast)
              have "is_hausdorff_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>C \<beta> \<subseteq> X\<close> hhaus
                by (by100 blast)
              have "finite {p}" by (by100 simp)
              have "{p} \<subseteq> C \<beta>" using \<open>p \<in> C \<beta>\<close> by (by100 blast)
              from Theorem_17_8[OF \<open>is_hausdorff_on (C \<beta>) _\<close> \<open>finite {p}\<close> \<open>{p} \<subseteq> C \<beta>\<close>]
              show ?thesis .
            qed
            ultimately show ?thesis by (by100 simp)
          next
            case False
            hence "C \<beta> \<inter> (C \<alpha> - {p}) = {}"
              using hdisjoint h\<alpha> h\<beta> by (by100 blast)
            hence "C \<beta> \<inter> (X - (C \<alpha> - {p})) = C \<beta>"
              using hC h\<beta> by (by100 blast)
            moreover have "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta>)"
            proof -
              have "C \<beta> \<subseteq> X" using hC h\<beta> by (by100 blast)
              have htop: "is_topology_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                by (rule subspace_topology_is_topology_on)
                   (use hstrict in \<open>unfold is_topology_on_strict_def, by100 blast\<close>,
                    use \<open>C \<beta> \<subseteq> X\<close> in blast)
              from closedin_carrier[OF htop] show ?thesis .
            qed
            ultimately show ?thesis by (by100 simp)
          qed
        qed
        from hweak[rule_format, OF hsub, THEN iffD2] this
        show ?thesis by (by100 blast)
      qed
      have "X - (C \<alpha> - {p}) \<subseteq> X" by (by100 blast)
      have "X - (X - (C \<alpha> - {p})) \<in> TX"
        using hcl unfolding closedin_on_def by (by100 blast)
      moreover have "X - (X - (C \<alpha> - {p})) = C \<alpha> - {p}"
        using hC h\<alpha> by (by100 blast)
      ultimately show "C \<alpha> - {p} \<in> TX" by (by100 simp)
    qed
    have hcompact_finite: "\<And>K. K \<subseteq> X \<Longrightarrow> top1_compact_on K (subspace_topology X TX K)
        \<Longrightarrow> finite {\<alpha>\<in>J. K \<inter> (C \<alpha> - {p}) \<noteq> {}}"
    proof -
      fix K assume hK_sub: "K \<subseteq> X" and hK_compact: "top1_compact_on K (subspace_topology X TX K)"
      let ?S = "{\<alpha>\<in>J. K \<inter> (C \<alpha> - {p}) \<noteq> {}}"
      show "finite ?S"
      proof (rule ccontr)
        assume "infinite ?S"
        \<comment> \<open>Pick x\\_\\<alpha> \\<in> K \\<inter> (C\\_\\<alpha> - {p}) for each \\<alpha> \\<in> ?S.\<close>
        have "\<forall>\<alpha>\<in>?S. \<exists>x. x \<in> K \<and> x \<in> C \<alpha> - {p}" by (by100 blast)
        hence "\<exists>xf. \<forall>\<alpha>\<in>?S. xf \<alpha> \<in> K \<and> xf \<alpha> \<in> C \<alpha> - {p}"
          by (rule bchoice)
        then obtain xf where hxf: "\<forall>\<alpha>\<in>?S. xf \<alpha> \<in> K \<and> xf \<alpha> \<in> C \<alpha> - {p}"
          by (by100 blast)
        let ?A = "xf ` ?S"
        \<comment> \<open>A is infinite (x\\_\\<alpha> pairwise distinct since C\\_\\<alpha> - {p} disjoint).\<close>
        have hinj: "inj_on xf ?S"
        proof (rule inj_onI)
          fix \<alpha> \<beta> assume "\<alpha> \<in> ?S" "\<beta> \<in> ?S" "xf \<alpha> = xf \<beta>"
          have "xf \<alpha> \<in> C \<alpha> - {p}" using hxf \<open>\<alpha> \<in> ?S\<close> by (by100 blast)
          have "xf \<beta> \<in> C \<beta> - {p}" using hxf \<open>\<beta> \<in> ?S\<close> by (by100 blast)
          have "xf \<alpha> \<in> C \<beta> - {p}" using \<open>xf \<alpha> = xf \<beta>\<close> \<open>xf \<beta> \<in> C \<beta> - {p}\<close> by (by100 simp)
          have "xf \<alpha> \<in> (C \<alpha> - {p}) \<inter> (C \<beta> - {p})"
            using \<open>xf \<alpha> \<in> C \<alpha> - {p}\<close> \<open>xf \<alpha> \<in> C \<beta> - {p}\<close> by (by100 blast)
          show "\<alpha> = \<beta>"
          proof (rule ccontr)
            assume "\<alpha> \<noteq> \<beta>"
            have "\<alpha> \<in> J" "\<beta> \<in> J" using \<open>\<alpha> \<in> ?S\<close> \<open>\<beta> \<in> ?S\<close> by (by100 blast)+
            from hdisjoint[rule_format, OF \<open>\<alpha> \<in> J\<close> \<open>\<beta> \<in> J\<close> \<open>\<alpha> \<noteq> \<beta>\<close>]
            have "C \<alpha> \<inter> C \<beta> = {p}" .
            hence "(C \<alpha> - {p}) \<inter> (C \<beta> - {p}) = {}" by (by100 blast)
            thus False using \<open>xf \<alpha> \<in> (C \<alpha> - {p}) \<inter> (C \<beta> - {p})\<close> by (by100 blast)
          qed
        qed
        have hA_inf: "infinite ?A"
        proof -
          from \<open>infinite ?S\<close> have "\<not> finite ?S" by simp
          moreover have "finite ?A \<Longrightarrow> finite ?S" using finite_imageD[OF _ hinj] by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        have hA_sub_K: "?A \<subseteq> K" using hxf by (by100 blast)
        \<comment> \<open>Key: every subset of A is closed in X (by coherent topology).
           For any B \\<subseteq> A and any \\<beta> \\<in> J: C\\_\\<beta> \\<inter> B \\<subseteq> {xf \\<beta>} which is finite \\<Rightarrow> closed in C\\_\\<beta>.\<close>
        have hA_every_sub_closed: "\<forall>B. B \<subseteq> ?A \<longrightarrow> closedin_on X TX B"
        proof (intro allI impI)
          fix B assume hB: "B \<subseteq> ?A"
          have hB_sub_X: "B \<subseteq> X" using hB hA_sub_K hK_sub by (by100 blast)
          show "closedin_on X TX B"
            using hweak[rule_format, OF hB_sub_X]
          proof (rule iffD2)
            show "\<forall>\<beta>\<in>J. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> B)"
            proof (intro ballI)
              fix \<beta> assume h\<beta>: "\<beta> \<in> J"
              have "C \<beta> \<inter> B \<subseteq> {xf \<beta>}"
              proof
                fix x assume "x \<in> C \<beta> \<inter> B"
                hence "x \<in> C \<beta>" "x \<in> B" by (by100 blast)+
                from \<open>x \<in> B\<close> hB obtain \<gamma> where "\<gamma> \<in> ?S" "x = xf \<gamma>" by (by100 blast)
                have "\<gamma> \<in> J" using \<open>\<gamma> \<in> ?S\<close> by (by100 blast)
                have "x \<in> C \<gamma> - {p}" using hxf \<open>\<gamma> \<in> ?S\<close> \<open>x = xf \<gamma>\<close> by (by100 blast)
                have "x \<in> C \<beta> \<inter> C \<gamma>" using \<open>x \<in> C \<beta>\<close> \<open>x \<in> C \<gamma> - {p}\<close> by (by100 blast)
                have "\<gamma> = \<beta>"
                proof (rule ccontr)
                  assume "\<gamma> \<noteq> \<beta>"
                  from hdisjoint[rule_format, OF \<open>\<beta> \<in> J\<close> \<open>\<gamma> \<in> J\<close>]
                  have "C \<beta> \<inter> C \<gamma> = {p}" using \<open>\<gamma> \<noteq> \<beta>\<close> by (by100 blast)
                  hence "x = p" using \<open>x \<in> C \<beta> \<inter> C \<gamma>\<close> by (by100 blast)
                  thus False using \<open>x \<in> C \<gamma> - {p}\<close> by (by100 blast)
                qed
                thus "x \<in> {xf \<beta>}" using \<open>x = xf \<gamma>\<close> by (by100 simp)
              qed
              \<comment> \<open>C\\_\\<beta> \\<inter> B is finite (\\<subseteq> {xf \\<beta>}), hence closed in Hausdorff C\\_\\<beta>.\<close>
              have "finite (C \<beta> \<inter> B)" using \<open>C \<beta> \<inter> B \<subseteq> {xf \<beta>}\<close>
                by (rule finite_subset) (by100 simp)
              have "C \<beta> \<subseteq> X" using hC h\<beta> by (by100 blast)
              have "is_hausdorff_on (C \<beta>) (subspace_topology X TX (C \<beta>))"
                using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>C \<beta> \<subseteq> X\<close> hhaus by (by100 blast)
              have "C \<beta> \<inter> B \<subseteq> C \<beta>" by (by100 blast)
              show "closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> B)"
                by (rule Theorem_17_8[OF \<open>is_hausdorff_on (C \<beta>) _\<close> \<open>finite (C \<beta> \<inter> B)\<close>
                    \<open>C \<beta> \<inter> B \<subseteq> C \<beta>\<close>])
            qed
          qed
        qed
        \<comment> \<open>A \\<subseteq> K infinite, every subset closed in X (hence in K).
           K compact Hausdorff \\<Rightarrow> limit point compact (Theorem 28.1).
           A infinite \\<Rightarrow> has limit point x in K.
           But A - {x} is closed in K \\<Rightarrow> K - (A - {x}) is open \\<ni> x,
           and (K - (A - {x})) \\<inter> (A - {x}) = {} \\<Rightarrow> x not a limit point. Contradiction.\<close>
        have hK_haus: "is_hausdorff_on K (subspace_topology X TX K)"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] hK_sub hhaus by (by100 blast)
        have hK_lpc: "top1_limit_point_compact_on K (subspace_topology X TX K)"
          by (rule Theorem_28_1[OF hK_compact])
        from hK_lpc[unfolded top1_limit_point_compact_on_def] hA_sub_K hA_inf
        obtain x where hx: "x \<in> K" and hx_lp: "is_limit_point_of x ?A K (subspace_topology X TX K)"
          by (by100 blast)
        \<comment> \<open>A - {x} is closed in X (every subset of A is closed).\<close>
        have "?A - {x} \<subseteq> ?A" by (by100 blast)
        from hA_every_sub_closed[rule_format, OF this]
        have hAmx_cl_X: "closedin_on X TX (?A - {x})" .
        \<comment> \<open>A - {x} closed in K (from closed in X + Theorem 17.2).\<close>
        have hTX_top: "is_topology_on X TX"
          using hstrict unfolding is_topology_on_strict_def by (by100 blast)
        from Theorem_17_2[OF hTX_top hK_sub]
        have "closedin_on K (subspace_topology X TX K) (?A - {x}) \<longleftrightarrow>
            (\<exists>D. closedin_on X TX D \<and> ?A - {x} = D \<inter> K)" .
        hence hAmx_cl_K: "closedin_on K (subspace_topology X TX K) (?A - {x})"
          using hAmx_cl_X hA_sub_K by (by100 blast)
        \<comment> \<open>K - (A - {x}) is open in K, contains x.\<close>
        have hopen_K: "K - (?A - {x}) \<in> subspace_topology X TX K"
          using hAmx_cl_K unfolding closedin_on_def by (by100 blast)
        have "x \<in> K - (?A - {x})" using hx by (by100 blast)
        \<comment> \<open>(K - (A - {x})) \\<inter> (A - {x}) = {} \\<Rightarrow> x is not a limit point of A.\<close>
        have "(K - (?A - {x})) \<inter> (?A - {x}) = {}" by (by100 blast)
        \<comment> \<open>But x IS a limit point: every open U \\<ni> x meets A - {x}.\<close>
        have "K - (?A - {x}) \<subseteq> K" by (by100 blast)
        have "K - (?A - {x}) \<in> subspace_topology X TX K" using hopen_K .
        \<comment> \<open>This open set contains x but is disjoint from A - {x}. Contradicts limit point.\<close>
        \<comment> \<open>x is a limit point of A, so every open U \\<ni> x meets A - {x}.
           But K - (A-{x}) is open, contains x, and is disjoint from A-{x}. Contradiction.\<close>
        from hx_lp[unfolded is_limit_point_of_def]
        have hlp_raw: "x \<in> K \<and> ?A \<subseteq> K \<and> (\<forall>U. neighborhood_of x K (subspace_topology X TX K) U
            \<longrightarrow> intersects (U - {x}) ?A)" by (by100 blast)
        have hlp: "\<forall>U. U \<in> subspace_topology X TX K \<longrightarrow> x \<in> U \<longrightarrow>
            (\<exists>y. y \<in> ?A \<and> y \<noteq> x \<and> y \<in> U)"
        proof (intro allI impI)
          fix U assume "U \<in> subspace_topology X TX K" "x \<in> U"
          have "neighborhood_of x K (subspace_topology X TX K) U"
            unfolding neighborhood_of_def using \<open>U \<in> _\<close> \<open>x \<in> U\<close> by (by100 blast)
          from hlp_raw \<open>neighborhood_of x K _ U\<close>
          have "intersects (U - {x}) ?A" by (by100 blast)
          thus "\<exists>y. y \<in> ?A \<and> y \<noteq> x \<and> y \<in> U"
            unfolding intersects_def by (by100 blast)
        qed
        from hlp[rule_format, OF hopen_K \<open>x \<in> K - (?A - {x})\<close>]
        obtain y where "y \<in> ?A" "y \<noteq> x" "y \<in> K - (?A - {x})" by (by100 blast)
        hence "y \<notin> ?A - {x}" by (by100 blast)
        hence "y = x" using \<open>y \<in> ?A\<close> by (by100 blast)
        thus False using \<open>y \<noteq> x\<close> by (by100 blast)
      qed
    qed
    have hloop_finite: "\<And>f. top1_is_loop_on X TX p f \<Longrightarrow>
        \<exists>F. finite F \<and> F \<subseteq> J \<and> f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>F. C \<alpha>)"
    proof -
      fix f assume hf: "top1_is_loop_on X TX p f"
      have hfI_sub: "f ` top1_unit_interval \<subseteq> X"
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def
          top1_continuous_map_on_def by (by100 blast)
      have hfI_compact: "top1_compact_on (f ` top1_unit_interval) (subspace_topology X TX (f ` top1_unit_interval))"
      proof -
        have hcont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
          using top1_unit_interval_topology_is_topology_on .
        have hTX_top: "is_topology_on X TX"
          using hstrict unfolding is_topology_on_strict_def by (by100 blast)
        have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          unfolding top1_unit_interval_def top1_unit_interval_topology_def
          using Theorem_27_1[of "0::real" 1] by (by100 simp)
        from Theorem_26_5[OF hI_top hTX_top hI_compact hcont]
        show ?thesis .
      qed
      let ?S = "{\<alpha>\<in>J. f ` top1_unit_interval \<inter> (C \<alpha> - {p}) \<noteq> {}}"
      from hcompact_finite[OF hfI_sub hfI_compact] have "finite ?S" .
      have "J \<noteq> {}" using hp hcover by (by100 blast)
      then obtain \<beta> where "\<beta> \<in> J" by (by100 blast)
      let ?F = "?S \<union> {\<beta>}"
      have "finite ?F" using \<open>finite ?S\<close> by (by100 simp)
      have "?F \<subseteq> J" using \<open>\<beta> \<in> J\<close> by (by100 blast)
      have "f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
      proof
        fix x assume "x \<in> f ` top1_unit_interval"
        hence "x \<in> X" using hfI_sub by (by100 blast)
        then obtain \<gamma> where "\<gamma> \<in> J" "x \<in> C \<gamma>" using hcover by (by100 blast)
        show "x \<in> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
        proof (cases "x = p")
          case True thus ?thesis using hC \<open>\<beta> \<in> J\<close> by (by100 blast)
        next
          case False
          hence "x \<in> C \<gamma> - {p}" using \<open>x \<in> C \<gamma>\<close> by (by100 blast)
          hence "\<gamma> \<in> ?S" using \<open>\<gamma> \<in> J\<close> \<open>x \<in> f ` top1_unit_interval\<close> by (by100 blast)
          thus ?thesis using \<open>x \<in> C \<gamma>\<close> by (by100 blast)
        qed
      qed
      thus "\<exists>F. finite F \<and> F \<subseteq> J \<and> f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>F. C \<alpha>)"
        using \<open>finite ?F\<close> \<open>?F \<subseteq> J\<close> by (by5000 blast)
    qed
    have hhtpy_finite: "\<And>f g. top1_is_loop_on X TX p f \<Longrightarrow> top1_is_loop_on X TX p g \<Longrightarrow>
        top1_path_homotopic_on X TX p p f g \<Longrightarrow>
        \<exists>F. finite F \<and> F \<subseteq> J \<and> top1_path_homotopic_on (\<Union>\<alpha>\<in>F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) p p f g"
    proof -
      fix f g assume hf: "top1_is_loop_on X TX p f" and hg: "top1_is_loop_on X TX p g"
        and hfg: "top1_path_homotopic_on X TX p p f g"
      \<comment> \<open>Extract homotopy H.\<close>
      from hfg[unfolded top1_path_homotopic_on_def]
      obtain H where hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX H"
        and hH0: "\<forall>s\<in>I_set. H (s, 0) = f s" and hH1: "\<forall>s\<in>I_set. H (s, 1) = g s"
        and hHl: "\<forall>t\<in>I_set. H (0, t) = p" and hHr: "\<forall>t\<in>I_set. H (1, t) = p"
        by (by100 blast)
      \<comment> \<open>II\\_topology = product\\_topology\\_on I\\_top I\\_top.\<close>
      have hH_cont': "top1_continuous_map_on (I_set \<times> I_set)
            (product_topology_on top1_unit_interval_topology top1_unit_interval_topology) X TX H"
        using hH_cont unfolding II_topology_def by (by100 simp)
      \<comment> \<open>H(I\\<times>I) is compact.\<close>
      have hHI_sub: "H ` (I_set \<times> I_set) \<subseteq> X"
        using hH_cont' unfolding top1_continuous_map_on_def by (by100 blast)
      have hHI_compact: "top1_compact_on (H ` (I_set \<times> I_set))
          (subspace_topology X TX (H ` (I_set \<times> I_set)))"
      proof -
        have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          unfolding top1_unit_interval_def top1_unit_interval_topology_def
          using Theorem_27_1[of "0::real" 1] by (by100 simp)
        have hII_compact: "top1_compact_on (I_set \<times> I_set)
            (product_topology_on top1_unit_interval_topology top1_unit_interval_topology)"
          by (rule Theorem_26_7[OF hI_compact hI_compact])
        have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
          using top1_unit_interval_topology_is_topology_on .
        have hII_top: "is_topology_on (I_set \<times> I_set)
            (product_topology_on top1_unit_interval_topology top1_unit_interval_topology)"
          using product_topology_on_is_topology_on[OF hI_top hI_top] .
        from Theorem_26_5[OF hII_top hTX hII_compact hH_cont']
        show ?thesis .
      qed
      \<comment> \<open>H(I\\<times>I) meets finitely many circles.\<close>
      from hcompact_finite[OF hHI_sub hHI_compact]
      have hH_fin: "finite {\<alpha>\<in>J. H ` (I_set \<times> I_set) \<inter> (C \<alpha> - {p}) \<noteq> {}}" .
      \<comment> \<open>Combine with hloop\\_finite for f and g.\<close>
      from hloop_finite[OF hf] obtain Ff where hFf: "finite Ff" "Ff \<subseteq> J"
          "f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>Ff. C \<alpha>)" by (by100 blast)
      from hloop_finite[OF hg] obtain Fg where hFg: "finite Fg" "Fg \<subseteq> J"
          "g ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>Fg. C \<alpha>)" by (by100 blast)
      let ?SH = "{\<alpha>\<in>J. H ` (I_set \<times> I_set) \<inter> (C \<alpha> - {p}) \<noteq> {}}"
      have "J \<noteq> {}" using hp hcover by (by100 blast)
      then obtain \<beta> where "\<beta> \<in> J" by (by100 blast)
      let ?F = "Ff \<union> Fg \<union> ?SH \<union> {\<beta>}"
      have "finite ?F" using hFf(1) hFg(1) hH_fin by (by100 simp)
      have "?F \<subseteq> J" using hFf(2) hFg(2) \<open>\<beta> \<in> J\<close> by (by100 blast)
      \<comment> \<open>H(I\\<times>I), f(I), g(I) all lie in \\<Union>?F C\\_\\<alpha>.\<close>
      have hH_in_F: "H ` (I_set \<times> I_set) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
      proof
        fix x assume "x \<in> H ` (I_set \<times> I_set)"
        hence "x \<in> X" using hHI_sub by (by100 blast)
        then obtain \<gamma> where "\<gamma> \<in> J" "x \<in> C \<gamma>" using hcover by (by100 blast)
        show "x \<in> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
        proof (cases "x = p")
          case True thus ?thesis using hC \<open>\<beta> \<in> J\<close> by (by100 blast)
        next
          case xFalse: False
          hence "x \<in> C \<gamma> - {p}" using \<open>x \<in> C \<gamma>\<close> by (by100 blast)
          hence "\<gamma> \<in> ?SH" using \<open>\<gamma> \<in> J\<close> \<open>x \<in> H ` (I_set \<times> I_set)\<close> by (by100 blast)
          thus ?thesis using \<open>x \<in> C \<gamma>\<close> by (by100 blast)
        qed
      qed
      \<comment> \<open>The homotopy restricts to \\<Union>?F C\\_\\<alpha> \\<Rightarrow> path homotopy in the subspace.\<close>
      have hF_sub: "(\<Union>\<alpha>\<in>?F. C \<alpha>) \<subseteq> X" using hC \<open>?F \<subseteq> J\<close> by (by100 blast)
      let ?Y = "\<Union>\<alpha>\<in>?F. C \<alpha>"
      let ?TY = "subspace_topology X TX ?Y"
      \<comment> \<open>H restricts to continuous map I\\<times>I \\<rightarrow> ?Y (subspace topology).\<close>
      have hII_top: "is_topology_on (I_set \<times> I_set) II_topology"
        unfolding II_topology_def
        using product_topology_on_is_topology_on[OF
          top1_unit_interval_topology_is_topology_on top1_unit_interval_topology_is_topology_on] .
      have hH_cont_sub: "top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H"
      proof -
        from Theorem_18_2(5)[OF hII_top hTX hTX, rule_format]
        show ?thesis using hH_cont hH_in_F hF_sub by (by100 blast)
      qed
      \<comment> \<open>f restricts to continuous path I \\<rightarrow> ?Y.\<close>
      have hI_top: "is_topology_on I_set I_top"
        using top1_unit_interval_topology_is_topology_on .
      have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hFf_sub_F: "Ff \<subseteq> ?F" by (by100 blast)
      have "(\<Union>\<alpha>\<in>Ff. C \<alpha>) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
        using hFf_sub_F by (by100 blast)
      have hf_im: "f ` I_set \<subseteq> ?Y"
        using hFf(3) \<open>(\<Union>\<alpha>\<in>Ff. C \<alpha>) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)\<close> by (by100 blast)
      have hf_cont_sub: "top1_continuous_map_on I_set I_top ?Y ?TY f"
      proof -
        from Theorem_18_2(5)[OF hI_top hTX hTX, rule_format]
        show ?thesis using hf_cont hf_im hF_sub by (by100 blast)
      qed
      have hf0: "f 0 = p" using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hf1: "f 1 = p" using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hf_path: "top1_is_path_on ?Y ?TY p p f"
        unfolding top1_is_path_on_def using hf_cont_sub hf0 hf1 by (by100 blast)
      \<comment> \<open>g restricts to continuous path I \\<rightarrow> ?Y.\<close>
      have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
        using hg unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hFg_sub_F: "Fg \<subseteq> ?F" by (by100 blast)
      have "(\<Union>\<alpha>\<in>Fg. C \<alpha>) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)"
        using hFg_sub_F by (by100 blast)
      have hg_im: "g ` I_set \<subseteq> ?Y"
        using hFg(3) \<open>(\<Union>\<alpha>\<in>Fg. C \<alpha>) \<subseteq> (\<Union>\<alpha>\<in>?F. C \<alpha>)\<close> by (by100 blast)
      have hg_cont_sub: "top1_continuous_map_on I_set I_top ?Y ?TY g"
      proof -
        from Theorem_18_2(5)[OF hI_top hTX hTX, rule_format]
        show ?thesis using hg_cont hg_im hF_sub by (by100 blast)
      qed
      have hg0: "g 0 = p" using hg unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hg1: "g 1 = p" using hg unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hg_path: "top1_is_path_on ?Y ?TY p p g"
        unfolding top1_is_path_on_def using hg_cont_sub hg0 hg1 by (by100 blast)
      \<comment> \<open>Package into path homotopy.\<close>
      have "top1_path_homotopic_on ?Y ?TY p p f g"
        unfolding top1_path_homotopic_on_def
        using hf_path hg_path hH_cont_sub hH0 hH1 hHl hHr by (by100 blast)
      show "\<exists>F. finite F \<and> F \<subseteq> J \<and> top1_path_homotopic_on (\<Union>\<alpha>\<in>F. C \<alpha>)
          (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) p p f g"
      proof (rule exI[of _ ?F], intro conjI)
        show "finite ?F" using \<open>finite ?F\<close> .
        show "?F \<subseteq> J" using \<open>?F \<subseteq> J\<close> .
        show "top1_path_homotopic_on (\<Union>\<alpha>\<in>?F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>?F. C \<alpha>)) p p f g"
          using \<open>top1_path_homotopic_on (\<Union>\<alpha>\<in>?F. C \<alpha>) _ p p f g\<close> .
      qed
    qed
    \<comment> \<open>For each finite F \\<subseteq> J, the sub-wedge is a wedge (hfinite\\_free).\<close>
    have hfinite_free: "\<And>F. finite F \<Longrightarrow> F \<subseteq> J \<Longrightarrow> F \<noteq> {} \<Longrightarrow>
        top1_is_wedge_of_circles_on (\<Union>\<alpha>\<in>F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) F p"
    proof -
      fix F assume hFfin: "finite F" and hFJ: "F \<subseteq> J" and hFne: "F \<noteq> {}"
      let ?Y = "\<Union>\<alpha>\<in>F. C \<alpha>"
      let ?TY = "subspace_topology X TX ?Y"
      have hY_sub: "?Y \<subseteq> X" using hC hFJ by (by100 blast)
      \<comment> \<open>Coherent topology for the sub-wedge: D \\<subseteq> ?Y closed in ?Y \\<longleftrightarrow>
         \\<forall>\\<alpha>\\<in>F. C\\_\\<alpha> \\<inter> D closed in C\\_\\<alpha>.
         Proof: D closed in ?Y \\<longleftrightarrow> D closed in X (by hweak, since for \\<alpha> \\<notin> F:
         C\\_\\<alpha> \\<inter> D \\<subseteq> {p} closed in Hausdorff C\\_\\<alpha>).
         Then D = D \\<inter> ?Y closed in subspace ?Y.\<close>
      have hcoh_F: "\<forall>D. D \<subseteq> ?Y \<longrightarrow>
          (closedin_on ?Y ?TY D \<longleftrightarrow>
           (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
      proof (intro allI impI iffI ballI)
        fix D \<alpha> assume hD: "D \<subseteq> ?Y" and hcl: "closedin_on ?Y ?TY D" and h\<alpha>: "\<alpha> \<in> F"
        \<comment> \<open>D closed in ?Y (subspace) \\<Longrightarrow> \\<exists>E closed in X with D = E \\<inter> ?Y.\<close>
        from Theorem_17_2[OF hTX hY_sub, THEN iffD1, OF hcl]
        obtain E where hE_cl: "closedin_on X TX E" and hDE: "D = E \<inter> ?Y" by (by100 blast)
        have hE_sub: "E \<subseteq> X" using hE_cl unfolding closedin_on_def by (by100 blast)
        from hweak[rule_format, OF hE_sub, THEN iffD1, OF hE_cl]
        have "\<forall>\<beta>\<in>J. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> E)" .
        hence "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> E)"
          using h\<alpha> hFJ by (by100 blast)
        moreover have "C \<alpha> \<inter> D = C \<alpha> \<inter> E"
          using \<open>D = E \<inter> ?Y\<close> h\<alpha> by (by100 blast)
        ultimately show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          by (by100 simp)
      next
        fix D assume hD: "D \<subseteq> ?Y"
          and hall: "\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
        \<comment> \<open>Show D closed in X by hweak. For \\<alpha> \\<in> F: given. For \\<alpha> \\<notin> F: C\\_\\<alpha> \\<inter> D \\<subseteq> {p}.\<close>
        have "\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
        proof (intro ballI)
          fix \<alpha> assume "\<alpha> \<in> J"
          show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          proof (cases "\<alpha> \<in> F")
            case True thus ?thesis using hall by (by100 blast)
          next
            case False
            have "C \<alpha> \<inter> D \<subseteq> C \<alpha> \<inter> ?Y" using hD by (by100 blast)
            also have "... \<subseteq> {p}"
            proof
              fix x assume "x \<in> C \<alpha> \<inter> ?Y"
              then obtain \<beta> where "\<beta> \<in> F" "x \<in> C \<alpha>" "x \<in> C \<beta>" by (by100 blast)
              have "\<alpha> \<noteq> \<beta>" using False \<open>\<beta> \<in> F\<close> by (by100 blast)
              from hdisjoint[rule_format, OF \<open>\<alpha> \<in> J\<close> _ \<open>\<alpha> \<noteq> \<beta>\<close>] \<open>\<beta> \<in> F\<close> hFJ
              have "C \<alpha> \<inter> C \<beta> = {p}" by (by100 blast)
              thus "x \<in> {p}" using \<open>x \<in> C \<alpha>\<close> \<open>x \<in> C \<beta>\<close> by (by100 blast)
            qed
            finally have "C \<alpha> \<inter> D \<subseteq> {p}" .
            have "finite (C \<alpha> \<inter> D)" using \<open>C \<alpha> \<inter> D \<subseteq> {p}\<close> finite_subset by (by100 blast)
            have "C \<alpha> \<subseteq> X" using hC \<open>\<alpha> \<in> J\<close> by (by100 blast)
            have "is_hausdorff_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
              using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>C \<alpha> \<subseteq> X\<close> hhaus by (by100 blast)
            have "C \<alpha> \<inter> D \<subseteq> C \<alpha>" by (by100 blast)
            show ?thesis
              by (rule Theorem_17_8[OF \<open>is_hausdorff_on (C \<alpha>) _\<close> \<open>finite (C \<alpha> \<inter> D)\<close>
                  \<open>C \<alpha> \<inter> D \<subseteq> C \<alpha>\<close>])
          qed
        qed
        hence "closedin_on X TX D" using hweak[rule_format, OF \<open>D \<subseteq> ?Y\<close>[THEN subset_trans[OF _ hY_sub]]]
          by (by100 blast)
        from Theorem_17_2[OF hTX hY_sub] this hD
        show "closedin_on ?Y ?TY D" by (by100 blast)
      qed
      show "top1_is_wedge_of_circles_on ?Y ?TY F p"
        unfolding top1_is_wedge_of_circles_on_def
      proof (intro conjI)
        show "is_topology_on_strict ?Y ?TY"
        proof -
          have "\<forall>U\<in>?TY. U \<subseteq> ?Y" unfolding subspace_topology_def by (by100 blast)
          moreover have "is_topology_on ?Y ?TY"
            by (rule subspace_topology_is_topology_on[OF hTX hY_sub])
          ultimately show ?thesis unfolding is_topology_on_strict_def by (by100 blast)
        qed
        show "is_hausdorff_on ?Y ?TY"
          using conjunct2[OF conjunct2[OF Theorem_17_11]] hY_sub hhaus by (by100 blast)
        show "p \<in> ?Y"
        proof -
          from hFne obtain \<beta> where "\<beta> \<in> F" by (by100 blast)
          hence "\<beta> \<in> J" using hFJ by (by100 blast)
          have "p \<in> C \<beta>" using hC \<open>\<beta> \<in> J\<close> by (by100 blast)
          thus ?thesis using \<open>\<beta> \<in> F\<close> by (by100 blast)
        qed
        show "\<exists>Ca. (\<forall>\<alpha>\<in>F. Ca \<alpha> \<subseteq> ?Y \<and> p \<in> Ca \<alpha>
            \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (Ca \<alpha>) (subspace_topology ?Y ?TY (Ca \<alpha>)) h))
          \<and> (\<Union>\<alpha>\<in>F. Ca \<alpha>) = ?Y
          \<and> (\<forall>\<alpha>\<in>F. \<forall>\<beta>\<in>F. \<alpha> \<noteq> \<beta> \<longrightarrow> Ca \<alpha> \<inter> Ca \<beta> = {p})
          \<and> (\<forall>D. D \<subseteq> ?Y \<longrightarrow> (closedin_on ?Y ?TY D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>F. closedin_on (Ca \<alpha>) (subspace_topology ?Y ?TY (Ca \<alpha>)) (Ca \<alpha> \<inter> D))))"
        proof (rule exI[of _ C], intro conjI)
          show "\<forall>\<alpha>\<in>F. C \<alpha> \<subseteq> ?Y \<and> p \<in> C \<alpha>
              \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) h)"
          proof (intro ballI conjI)
            fix \<alpha> assume "\<alpha> \<in> F"
            hence "\<alpha> \<in> J" using hFJ by (by100 blast)
            show "C \<alpha> \<subseteq> ?Y" using \<open>\<alpha> \<in> F\<close> by (by100 blast)
            show "p \<in> C \<alpha>" using hC \<open>\<alpha> \<in> J\<close> by (by100 blast)
            show "\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) h"
            proof -
              from hC[rule_format, OF \<open>\<alpha> \<in> J\<close>]
              obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h" by (by100 blast)
              have "subspace_topology ?Y ?TY (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
                by (rule subspace_topology_trans) (use \<open>\<alpha> \<in> F\<close> in blast)
              have "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) h"
                using hh \<open>subspace_topology ?Y ?TY (C \<alpha>) = subspace_topology X TX (C \<alpha>)\<close>
                by (by100 simp)
              thus ?thesis by (by100 blast)
            qed
          qed
          show "(\<Union>\<alpha>\<in>F. C \<alpha>) = ?Y" by (by100 blast)
          show "\<forall>\<alpha>\<in>F. \<forall>\<beta>\<in>F. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
            using hdisjoint hFJ by (by100 blast)
          show "\<forall>D. D \<subseteq> ?Y \<longrightarrow> (closedin_on ?Y ?TY D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) (C \<alpha> \<inter> D)))"
          proof (intro allI impI)
            fix D assume "D \<subseteq> ?Y"
            from hcoh_F[rule_format, OF this]
            have "closedin_on ?Y ?TY D \<longleftrightarrow>
                (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D))" .
            moreover have "\<forall>\<alpha>\<in>F. subspace_topology ?Y ?TY (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
            proof (intro ballI)
              fix \<alpha> assume "\<alpha> \<in> F"
              show "subspace_topology ?Y ?TY (C \<alpha>) = subspace_topology X TX (C \<alpha>)"
                by (rule subspace_topology_trans) (use \<open>\<alpha> \<in> F\<close> in blast)
            qed
            ultimately show "closedin_on ?Y ?TY D \<longleftrightarrow>
                (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology ?Y ?TY (C \<alpha>)) (C \<alpha> \<inter> D))"
              by (by100 simp)
          qed
        qed
      qed
    qed
    \<comment> \<open>Coherent topology for sub-wedges (same proof as inside hfinite\\_free, exposed separately).\<close>
    have hcoh_sub: "\<And>F. F \<subseteq> J \<Longrightarrow>
        (\<forall>D. D \<subseteq> (\<Union>\<alpha>\<in>F. C \<alpha>) \<longrightarrow>
          (closedin_on (\<Union>\<alpha>\<in>F. C \<alpha>) (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) D \<longleftrightarrow>
           (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D))))"
    proof -
      fix F assume hFJ: "F \<subseteq> J"
      let ?Y = "\<Union>\<alpha>\<in>F. C \<alpha>"
      let ?TY = "subspace_topology X TX ?Y"
      have hY_sub: "?Y \<subseteq> X" using hC hFJ by (by100 blast)
      show "\<forall>D. D \<subseteq> ?Y \<longrightarrow> (closedin_on ?Y ?TY D \<longleftrightarrow>
          (\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
      proof (intro allI impI iffI ballI)
        fix D \<alpha> assume hD: "D \<subseteq> ?Y" and hcl: "closedin_on ?Y ?TY D" and h\<alpha>: "\<alpha> \<in> F"
        from Theorem_17_2[OF hTX hY_sub, THEN iffD1, OF hcl]
        obtain E where hE_cl: "closedin_on X TX E" and hDE: "D = E \<inter> ?Y" by (by100 blast)
        have hE_sub: "E \<subseteq> X" using hE_cl unfolding closedin_on_def by (by100 blast)
        from hweak[rule_format, OF hE_sub, THEN iffD1, OF hE_cl]
        have "\<forall>\<beta>\<in>J. closedin_on (C \<beta>) (subspace_topology X TX (C \<beta>)) (C \<beta> \<inter> E)" .
        hence "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> E)"
          using h\<alpha> hFJ by (by100 blast)
        moreover have "C \<alpha> \<inter> D = C \<alpha> \<inter> E" using \<open>D = E \<inter> ?Y\<close> h\<alpha> by (by100 blast)
        ultimately show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          by (by100 simp)
      next
        fix D assume hD: "D \<subseteq> ?Y"
          and hall: "\<forall>\<alpha>\<in>F. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
        have "\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
        proof (intro ballI)
          fix \<alpha> assume "\<alpha> \<in> J"
          show "closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)"
          proof (cases "\<alpha> \<in> F")
            case True thus ?thesis using hall by (by100 blast)
          next
            case False
            have "C \<alpha> \<inter> D \<subseteq> C \<alpha> \<inter> ?Y" using hD by (by100 blast)
            also have "... \<subseteq> {p}"
            proof
              fix x assume "x \<in> C \<alpha> \<inter> ?Y"
              then obtain \<beta> where "\<beta> \<in> F" "x \<in> C \<alpha>" "x \<in> C \<beta>" by (by100 blast)
              have "\<alpha> \<noteq> \<beta>" using False \<open>\<beta> \<in> F\<close> by (by100 blast)
              from hdisjoint[rule_format, OF \<open>\<alpha> \<in> J\<close> _ \<open>\<alpha> \<noteq> \<beta>\<close>] \<open>\<beta> \<in> F\<close> hFJ
              have "C \<alpha> \<inter> C \<beta> = {p}" by (by100 blast)
              thus "x \<in> {p}" using \<open>x \<in> C \<alpha>\<close> \<open>x \<in> C \<beta>\<close> by (by100 blast)
            qed
            finally have "C \<alpha> \<inter> D \<subseteq> {p}" .
            have "finite (C \<alpha> \<inter> D)" using \<open>C \<alpha> \<inter> D \<subseteq> {p}\<close> finite_subset by (by100 blast)
            have "C \<alpha> \<subseteq> X" using hC \<open>\<alpha> \<in> J\<close> by (by100 blast)
            have "is_hausdorff_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
              using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>C \<alpha> \<subseteq> X\<close> hhaus by (by100 blast)
            have "C \<alpha> \<inter> D \<subseteq> C \<alpha>" by (by100 blast)
            show ?thesis
              by (rule Theorem_17_8[OF \<open>is_hausdorff_on (C \<alpha>) _\<close> \<open>finite (C \<alpha> \<inter> D)\<close>
                  \<open>C \<alpha> \<inter> D \<subseteq> C \<alpha>\<close>])
          qed
        qed
        hence "closedin_on X TX D"
          using hweak[rule_format, OF \<open>D \<subseteq> ?Y\<close>[THEN subset_trans[OF _ hY_sub]]]
          by (by100 blast)
        from Theorem_17_2[OF hTX hY_sub] this hD
        show "closedin_on ?Y ?TY D" by (by100 blast)
      qed
    qed
    \<comment> \<open>Now verify top1\\_is\\_free\\_group\\_full\\_on for \\<pi>\\_1(X, p).
       For each finite sub-wedge F, Theorem\\_71\\_3\\_finite gives \\<pi>\\_1 free on F.
       The free group condition 5 (no reduced word = id): a word w uses finitely many
       generators {\\<alpha>\\_1,...,\\<alpha>\\_n}. Take F containing these. The sub-wedge \\<Union>F C\\_\\<alpha>
       has \\<pi>\\_1 free on F (Theorem 71.1). The word is non-trivial there.
       The inclusion \\<pi>\\_1(sub-wedge) \\<hookrightarrow> \\<pi>\\_1(X) is injective (by hhtpy\\_finite:
       if a loop in the sub-wedge is null-homotopic in X, the homotopy lies in a finite
       sub-wedge, so the loop is null-homotopic in the sub-wedge).
       Therefore the word is non-trivial in \\<pi>\\_1(X).\<close>
    \<comment> \<open>Define \\<iota>(\\<alpha>) = the loop class of the S1 generator in C\\_\\<alpha>, included into X.\<close>
    \<comment> \<open>For each \\<alpha> \\<in> J, C\\_\\<alpha> \\<cong> S1, so \\<pi>\\_1(C\\_\\<alpha>, p) \\<cong> Z, generated by some loop f\\_\\<alpha>.
       The inclusion i\\_\\<alpha>: C\\_\\<alpha> \\<hookrightarrow> X induces a hom \\<pi>\\_1(C\\_\\<alpha>) \\<rightarrow> \\<pi>\\_1(X).
       Set \\<iota>(\\<alpha>) = [f\\_\\<alpha>] in \\<pi>\\_1(X, p).\<close>
    \<comment> \<open>Step 1: choose generator loops.\<close>
    \<comment> \<open>Step 1-2: choose generator loops and define \\<iota>.
       For each \\<alpha> \\<in> J, C\\_\\<alpha> \\<cong> S1 has \\<pi>\\_1(C\\_\\<alpha>) \\<cong> Z generated by some loop f\\_\\<alpha>.
       The inclusion C\\_\\<alpha> \\<hookrightarrow> X gives f\\_\\<alpha> as a loop in X with image in C\\_\\<alpha>.\<close>
    \<comment> \<open>For each \\<alpha>, the homeomorphism h\\_\\<alpha>: S1 \\<rightarrow> C\\_\\<alpha> may not send (1,0) to p.
       We compose h\\_\\<alpha> with a rotation to get g\\_\\<alpha> with g\\_\\<alpha>(1,0) = p.
       Then gen\\_loop \\<alpha> t = g\\_\\<alpha>(cos(2\\<pi>t), sin(2\\<pi>t)) is a loop in C\\_\\<alpha> based at p.\<close>
    \<comment> \<open>First, obtain homeomorphisms g\\_\\<alpha> with g\\_\\<alpha>(1,0) = p.\<close>
    have hg_ex: "\<forall>\<alpha>\<in>J. \<exists>g. top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology X TX (C \<alpha>)) g \<and> g (1, 0) = p"
    proof (intro ballI)
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
      from hC[rule_format, OF h\<alpha>]
      obtain h where hh: "top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h" and hCsub: "C \<alpha> \<subseteq> X" and hpC: "p \<in> C \<alpha>"
        by (by100 blast)
      \<comment> \<open>h is bijective S1 \\<rightarrow> C\\_\\<alpha>. Since p \\<in> C\\_\\<alpha>, there exists q \\<in> S1 with h(q) = p.\<close>
      have hh_bij: "bij_betw h top1_S1 (C \<alpha>)"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hh_surj: "h ` top1_S1 = C \<alpha>"
        using hh_bij unfolding bij_betw_def by (by100 blast)
      from hpC have "p \<in> h ` top1_S1" using hh_surj by (by100 simp)
      then obtain q where hq_S1: "q \<in> top1_S1" and hhq: "h q = p" by (by100 blast)
      obtain a b where hq_eq: "q = (a, b)" by (cases q) (by100 blast)
      have hab: "a * a + b * b = 1"
      proof -
        have "a^2 + b^2 = 1" using hq_S1 unfolding hq_eq top1_S1_def by (by100 simp)
        thus ?thesis unfolding power2_eq_square .
      qed
      \<comment> \<open>Define rotation R(x,y) = (a*x - b*y, b*x + a*y). R(1,0) = (a,b) = q.\<close>
      define R where "R z = (a * fst z - b * snd z, b * fst z + a * snd z)" for z
      have hR10: "R (1, 0) = q" unfolding R_def hq_eq by (by100 simp)
      \<comment> \<open>R maps S1 to S1.\<close>
      have hR_S1: "\<forall>z\<in>top1_S1. R z \<in> top1_S1"
      proof (intro ballI)
        fix z assume hz: "z \<in> top1_S1"
        have hzn: "fst z * fst z + snd z * snd z = 1"
        proof -
          have "(fst z)^2 + (snd z)^2 = 1" using hz unfolding top1_S1_def by (by100 simp)
          thus ?thesis unfolding power2_eq_square .
        qed
        have "fst (R z) * fst (R z) + snd (R z) * snd (R z) =
            (a * fst z - b * snd z) * (a * fst z - b * snd z) +
            (b * fst z + a * snd z) * (b * fst z + a * snd z)"
          unfolding R_def by (by100 simp)
        also have "... = (a*a + b*b) * (fst z * fst z + snd z * snd z)"
          by (by100 algebra)
        also have "... = 1" using hab hzn by (by100 simp)
        finally have "fst (R z) * fst (R z) + snd (R z) * snd (R z) = 1" .
        hence "(fst (R z))^2 + (snd (R z))^2 = 1" unfolding power2_eq_square .
        thus "R z \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      qed
      \<comment> \<open>R is bijective on S1. Inverse is R'(x,y) = (a*x + b*y, -b*x + a*y).\<close>
      define R' where "R' z = (a * fst z + b * snd z, -(b * fst z) + a * snd z)" for z
      have hR'_S1: "\<forall>z\<in>top1_S1. R' z \<in> top1_S1"
      proof (intro ballI)
        fix z assume hz: "z \<in> top1_S1"
        have hzn: "fst z * fst z + snd z * snd z = 1"
        proof -
          have "(fst z)^2 + (snd z)^2 = 1" using hz unfolding top1_S1_def by (by100 simp)
          thus ?thesis unfolding power2_eq_square .
        qed
        have "fst (R' z) * fst (R' z) + snd (R' z) * snd (R' z) =
            (a * fst z + b * snd z) * (a * fst z + b * snd z) +
            (-(b * fst z) + a * snd z) * (-(b * fst z) + a * snd z)"
          unfolding R'_def by (by100 simp)
        also have "... = (a*a + b*b) * (fst z * fst z + snd z * snd z)"
          by (by100 algebra)
        also have "... = 1" using hab hzn by (by100 simp)
        finally have "fst (R' z) * fst (R' z) + snd (R' z) * snd (R' z) = 1" .
        hence "(fst (R' z))^2 + (snd (R' z))^2 = 1" unfolding power2_eq_square .
        thus "R' z \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      qed
      have hRR': "\<forall>z\<in>top1_S1. R' (R z) = z"
      proof (intro ballI)
        fix z assume "z \<in> top1_S1"
        have "fst (R' (R z)) = a * (a * fst z - b * snd z) + b * (b * fst z + a * snd z)"
          unfolding R_def R'_def by (by100 simp)
        also have "... = (a*a + b*b) * fst z" by (by100 algebra)
        also have "... = fst z" using hab by (by100 simp)
        finally have h1: "fst (R' (R z)) = fst z" .
        have "snd (R' (R z)) = -(b * (a * fst z - b * snd z)) + a * (b * fst z + a * snd z)"
          unfolding R_def R'_def by (by100 simp)
        also have "... = (a*a + b*b) * snd z" by (by100 algebra)
        also have "... = snd z" using hab by (by100 simp)
        finally have h2: "snd (R' (R z)) = snd z" .
        show "R' (R z) = z" using h1 h2 by (rule prod_eqI)
      qed
      have hR'R: "\<forall>z\<in>top1_S1. R (R' z) = z"
      proof (intro ballI)
        fix z assume "z \<in> top1_S1"
        have "fst (R (R' z)) = a * (a * fst z + b * snd z) - b * (-(b * fst z) + a * snd z)"
          unfolding R_def R'_def by (by100 simp)
        also have "... = (a*a + b*b) * fst z" by (by100 algebra)
        also have "... = fst z" using hab by (by100 simp)
        finally have h1: "fst (R (R' z)) = fst z" .
        have "snd (R (R' z)) = b * (a * fst z + b * snd z) + a * (-(b * fst z) + a * snd z)"
          unfolding R_def R'_def by (by100 simp)
        also have "... = (a*a + b*b) * snd z" by (by100 algebra)
        also have "... = snd z" using hab by (by100 simp)
        finally have h2: "snd (R (R' z)) = snd z" .
        show "R (R' z) = z" using h1 h2 by (rule prod_eqI)
      qed
      have hR_bij: "bij_betw R top1_S1 top1_S1"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on R top1_S1"
        proof (rule inj_onI)
          fix x y assume "x \<in> top1_S1" "y \<in> top1_S1" "R x = R y"
          hence "R' (R x) = R' (R y)" by (by100 simp)
          thus "x = y" using hRR' \<open>x \<in> top1_S1\<close> \<open>y \<in> top1_S1\<close> by (by100 simp)
        qed
        show "R ` top1_S1 = top1_S1"
        proof
          show "R ` top1_S1 \<subseteq> top1_S1" using hR_S1 by (by100 blast)
          show "top1_S1 \<subseteq> R ` top1_S1"
          proof
            fix z assume "z \<in> top1_S1"
            hence "R' z \<in> top1_S1" using hR'_S1 by (by100 blast)
            have "R (R' z) = z" using hR'R \<open>z \<in> top1_S1\<close> by (by100 blast)
            hence "z = R (R' z)" by (by100 simp)
            thus "z \<in> R ` top1_S1" using \<open>R' z \<in> top1_S1\<close> by (rule image_eqI)
          qed
        qed
      qed
      \<comment> \<open>R is continuous on S1 (restriction of polynomial map on R2).
         Use Theorem 26.6: continuous bijection from compact to Hausdorff.\<close>
      have hR_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
          top1_S1 top1_S1_topology R"
      proof -
        \<comment> \<open>R is continuous on all of R2 (linear map).\<close>
        have "continuous_on UNIV R"
          unfolding R_def
          by (intro continuous_intros)
        \<comment> \<open>Use bridge lemma: continuous\\_on UNIV + maps S1 \\<rightarrow> S1 \\<Longrightarrow> top1\\_continuous.\<close>
        from top1_continuous_map_on_real2_subspace[OF _ this]
        show ?thesis unfolding top1_S1_topology_def using hR_S1 by (by100 blast)
      qed
      have hR_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
          top1_S1 top1_S1_topology R"
      proof -
        have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
          using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hS1_compact: "top1_compact_on top1_S1 top1_S1_topology"
          using S1_compact .
        have hS1_haus: "is_hausdorff_on top1_S1 top1_S1_topology"
          using top1_S1_is_hausdorff .
        show ?thesis
          by (rule Theorem_26_6[OF hS1_top hS1_top hS1_compact hS1_haus hR_cont hR_bij])
      qed
      \<comment> \<open>Compose: g = h \\<circ> R has g(1,0) = h(q) = p.\<close>
      define g where "g = h \<circ> R"
      have "top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) g"
        unfolding g_def by (rule homeomorphism_comp[OF hR_homeo hh])
      moreover have "g (1, 0) = p" unfolding g_def comp_def using hR10 hhq by (by100 simp)
      ultimately show "\<exists>g. top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) g \<and> g (1, 0) = p" by (by100 blast)
    qed
    obtain g where hg: "\<forall>\<alpha>\<in>J. top1_homeomorphism_on top1_S1 top1_S1_topology
        (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (g \<alpha>) \<and> (g \<alpha>) (1, 0) = p"
      using bchoice[OF hg_ex] by (by100 blast)
    \<comment> \<open>Define gen\\_loop \\<alpha> t = g\\_\\<alpha>(cos(2\\<pi>t), sin(2\\<pi>t)). This is a loop in C\\_\\<alpha> based at p.\<close>
    define gen_loop where "gen_loop \<alpha> t = (g \<alpha>) (cos (2 * pi * t), sin (2 * pi * t))" for \<alpha> t
    have hgen: "\<forall>\<alpha>\<in>J. top1_is_loop_on X TX p (gen_loop \<alpha>) \<and>
        (gen_loop \<alpha>) ` top1_unit_interval \<subseteq> C \<alpha>"
    proof (intro ballI conjI)
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> J"
      have hg\<alpha>: "top1_homeomorphism_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (g \<alpha>)" "(g \<alpha>) (1, 0) = p"
        using hg h\<alpha> by (by100 blast)+
      have hC\<alpha>: "C \<alpha> \<subseteq> X" "p \<in> C \<alpha>" using hC h\<alpha> by (by100 blast)+
      have hTC\<alpha>: "is_topology_on (C \<alpha>) (subspace_topology X TX (C \<alpha>))"
        by (rule subspace_topology_is_topology_on[OF hTX hC\<alpha>(1)])
      \<comment> \<open>The standard S1 loop is a loop on S1. Composing with g\\_\\<alpha> gives a loop on C\\_\\<alpha>.\<close>
      have hstd: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
          (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s)))"
        by (rule standard_S1_loop_is_loop)
      \<comment> \<open>g\\_\\<alpha> is continuous S1 \\<rightarrow> C\\_\\<alpha>, and the standard loop is continuous I \\<rightarrow> S1.\<close>
      have hg\<alpha>_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (g \<alpha>)"
        using hg\<alpha>(1) unfolding top1_homeomorphism_on_def by (by100 blast)
      have hstd_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology
          (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s)))"
        using hstd unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      \<comment> \<open>Composition: gen\\_loop \\<alpha> is continuous I \\<rightarrow> C\\_\\<alpha>.\<close>
      have hcomp: "top1_continuous_map_on I_set I_top
          (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (gen_loop \<alpha>)"
      proof -
        have "top1_continuous_map_on I_set I_top
            (C \<alpha>) (subspace_topology X TX (C \<alpha>))
            ((g \<alpha>) \<circ> (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))))"
          by (rule top1_continuous_map_on_comp[OF hstd_cont hg\<alpha>_cont])
        moreover have "(g \<alpha>) \<circ> (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) = gen_loop \<alpha>"
          unfolding gen_loop_def comp_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Lift to X via inclusion C\\_\\<alpha> \\<hookrightarrow> X.\<close>
      have hincl: "top1_continuous_map_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) X TX id"
        using Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hC\<alpha>(1)] .
      have hgen_cont_X: "top1_continuous_map_on I_set I_top X TX (gen_loop \<alpha>)"
      proof -
        have "top1_continuous_map_on I_set I_top X TX (id \<circ> gen_loop \<alpha>)"
          by (rule top1_continuous_map_on_comp[OF hcomp hincl])
        thus ?thesis by (by100 simp)
      qed
      show "top1_is_loop_on X TX p (gen_loop \<alpha>)"
        unfolding top1_is_loop_on_def top1_is_path_on_def
        using hgen_cont_X hg\<alpha>(2) unfolding gen_loop_def by (by100 simp)
      show "(gen_loop \<alpha>) ` top1_unit_interval \<subseteq> C \<alpha>"
      proof
        fix x assume "x \<in> gen_loop \<alpha> ` top1_unit_interval"
        then obtain t where "t \<in> top1_unit_interval" "x = gen_loop \<alpha> t" by (by100 blast)
        have "(cos (2 * pi * t), sin (2 * pi * t)) \<in> top1_S1"
          unfolding top1_S1_def by (by100 simp)
        hence "x \<in> C \<alpha>" using \<open>x = gen_loop \<alpha> t\<close>
          hg\<alpha>(1)[unfolded top1_homeomorphism_on_def top1_continuous_map_on_def]
          unfolding gen_loop_def by (by100 blast)
        thus "x \<in> C \<alpha>" .
      qed
    qed
    \<comment> \<open>Inclusion injectivity: the inclusion hom \\<pi>\\_1(\\<Union>F) \\<rightarrow> \\<pi>\\_1(X) is injective.
       Book: if f is a loop in \\<Union>F that is null-homotopic in X, then it is
       null-homotopic in some \\<Union>F' \\<supseteq> \\<Union>F, hence in \\<Union>F by Theorem 71.1.\<close>
    have hincl_inj: "\<And>F. finite F \<Longrightarrow> F \<subseteq> J \<Longrightarrow> F \<noteq> {} \<Longrightarrow>
        inj_on (top1_fundamental_group_induced_on (\<Union>\<alpha>\<in>F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) p X TX p (\<lambda>x. x))
          (top1_fundamental_group_carrier (\<Union>\<alpha>\<in>F. C \<alpha>)
            (subspace_topology X TX (\<Union>\<alpha>\<in>F. C \<alpha>)) p)"
    proof -
      fix F assume hFfin: "finite F" and hFJ: "F \<subseteq> J" and hFne: "F \<noteq> {}"
      let ?Y = "\<Union>\<alpha>\<in>F. C \<alpha>"
      let ?TY = "subspace_topology X TX ?Y"
      let ?incl = "top1_fundamental_group_induced_on ?Y ?TY p X TX p (\<lambda>x. x)"
      have hY_sub: "?Y \<subseteq> X" using hC hFJ by (by100 blast)
      have hpY: "p \<in> ?Y" using hFne hC hFJ by (by100 blast)
      have hTY: "is_topology_on ?Y ?TY" by (rule subspace_topology_is_topology_on[OF hTX hY_sub])
      \<comment> \<open>\\<pi>\\_1(?Y) is free on F via chosen\\_loops\\_arb.\<close>
      from hfinite_free[OF hFfin hFJ hFne]
      have hwedge_Y: "top1_is_wedge_of_circles_on ?Y ?TY F p" .
      have hg_F: "\<forall>j\<in>F. top1_homeomorphism_on top1_S1 top1_S1_topology
          (C j) (subspace_topology ?Y ?TY (C j)) (g j)"
      proof -
        { fix j assume "j \<in> F"
          hence "j \<in> J" using hFJ by (by100 blast)
          have "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
          moreover have "subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
            by (rule subspace_topology_trans) (use \<open>j \<in> F\<close> in blast)
          ultimately have "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology ?Y ?TY (C j)) (g j)" by (by100 simp) }
        thus ?thesis by (by100 blast)
      qed
      have hC_closed_F: "\<forall>D\<subseteq>?Y. closedin_on ?Y ?TY D \<longleftrightarrow>
          (\<forall>j\<in>F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D))"
      proof (intro allI impI iffI)
        fix D assume hD: "D \<subseteq> ?Y"
        from hcoh_sub[OF hFJ, rule_format, OF hD]
        have hiff: "closedin_on ?Y ?TY D \<longleftrightarrow>
            (\<forall>j\<in>F. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
        have htrans: "\<forall>j\<in>F. subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
          by (intro ballI, rule subspace_topology_trans) blast
        show "closedin_on ?Y ?TY D \<Longrightarrow>
            \<forall>j\<in>F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D)"
          using hiff htrans by (by100 simp)
        show "(\<forall>j\<in>F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D)) \<Longrightarrow>
            closedin_on ?Y ?TY D"
          using hiff htrans by (by100 simp)
      qed
      have hbase_F: "\<forall>j\<in>F. g j (1, 0) = p" using hg hFJ by (by100 blast)
      have hC_data_F: "\<forall>j\<in>F. C j \<subseteq> ?Y \<and> p \<in> C j" using hC hFJ by (by100 blast)
      have hC_union_F: "(\<Union>j\<in>F. C j) = ?Y" by (by100 blast)
      have hC_disj_F: "\<forall>i\<in>F. \<forall>j\<in>F. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
        using hdisjoint hFJ by (by100 blast)
      from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge_Y hFfin
          hg_F hbase_F hC_data_F hC_union_F hC_disj_F hC_closed_F]
      obtain GF :: "int set" and mulF eF invgF and \<eta>F :: "'i \<Rightarrow> int" and \<Phi>F
        where hfreeF: "top1_is_free_group_full_on GF mulF eF invgF \<eta>F F"
          and hisoF: "top1_group_iso_on GF mulF
              (top1_fundamental_group_carrier ?Y ?TY p) (top1_fundamental_group_mul ?Y ?TY p) \<Phi>F"
          and hgensF: "\<forall>j\<in>F. \<Phi>F (\<eta>F j) = {l. top1_loop_equiv_on ?Y ?TY p
              (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
        by (by100 blast)
      \<comment> \<open>The inclusion \\<pi>\\_1(?Y) \\<rightarrow> \\<pi>\\_1(X) is a group hom.\<close>
      have hincl_hom: "top1_group_hom_on
          (top1_fundamental_group_carrier ?Y ?TY p) (top1_fundamental_group_mul ?Y ?TY p)
          (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p) ?incl"
        by (rule subspace_inclusion_induced_hom[OF hTX hY_sub hpY])
      \<comment> \<open>Suppose ?incl(c) = ?incl(c') for c, c' \\<in> \\<pi>\\_1(?Y). Need c = c'.
         Equivalently: ker(?incl) = {id}. I.e., ?incl(c) = id\\_X \\<Longrightarrow> c = id\\_Y.

         We prove: ?incl(c) = id\\_X \\<Longrightarrow> c = id\\_Y.
         The composition \\<Phi>\\_F\<inverse> \\<circ> ?incl \\<circ> \\<Phi>\\_F: free(F) \\<rightarrow> \\<pi>\\_1(X).
         If this sends x \\<mapsto> id\\_X, then by applying free\\_group\\_word\\_kernel
         in the reverse direction... no, we use the subgroup\\_generated representation
         + free\\_group\\_word\\_kernel of free(F\\<union>F') to derive x = eF.\<close>
      show "inj_on ?incl (top1_fundamental_group_carrier ?Y ?TY p)"
      proof (rule inj_onI)
        fix c1 c2 assume hc1: "c1 \<in> top1_fundamental_group_carrier ?Y ?TY p"
          and hc2: "c2 \<in> top1_fundamental_group_carrier ?Y ?TY p"
          and heq: "?incl c1 = ?incl c2"
        \<comment> \<open>Sufficient to show: if ?incl(c) = id\\_X then c = id\\_Y.
           Then ?incl(c1 * c2\<inverse>) = ?incl(c1) * ?incl(c2)\<inverse> = id, so c1 * c2\<inverse> = id, so c1 = c2.\<close>
        \<comment> \<open>Alternative: directly show c1 = c2 from ?incl(c1) = ?incl(c2).\<close>
        \<comment> \<open>?incl(c1) = ?incl(c2) means: for loops f1 \\<in> c1, f2 \\<in> c2, f1 ~ f2 in X.\<close>
        \<comment> \<open>By hhtpy\\_finite, f1 ~ f2 in \\<Union>F'. In \\<Union>(F\\<union>F'), f1 ~ f2.
           So [f1] = [f2] in \\<pi>\\_1(\\<Union>(F\\<union>F')).
           The inclusion \\<pi>\\_1(\\<Union>F) \\<rightarrow> \\<pi>\\_1(\\<Union>(F\\<union>F')) sends c1 \\<mapsto> [f1], c2 \\<mapsto> [f2].
           So inclusion(c1) = inclusion(c2) in \\<pi>\\_1(\\<Union>(F\\<union>F')).
           Need: this inclusion is injective. This is the free group embedding.
           Use: free\\_group\\_word\\_kernel on free(F\\<union>F') with target free(F).\<close>
        \<comment> \<open>Extract representative loops and use hhtpy\\_finite.\<close>
        from hc1[unfolded top1_fundamental_group_carrier_def]
        obtain f1 where hf1_loop: "top1_is_loop_on ?Y ?TY p f1"
            and hc1_eq: "c1 = {g. top1_loop_equiv_on ?Y ?TY p f1 g}" by (by100 blast)
        from hc2[unfolded top1_fundamental_group_carrier_def]
        obtain f2 where hf2_loop: "top1_is_loop_on ?Y ?TY p f2"
            and hc2_eq: "c2 = {g. top1_loop_equiv_on ?Y ?TY p f2 g}" by (by100 blast)
        \<comment> \<open>incl(c1) = incl(c2) means f1 ~ f2 in X.\<close>
        have hf1X: "top1_is_loop_on X TX p f1"
        proof -
          have hf1_cont_Y: "top1_continuous_map_on I_set I_top ?Y ?TY f1"
            using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have "top1_continuous_map_on I_set I_top X TX (id \<circ> f1)"
            by (rule top1_continuous_map_on_comp[OF hf1_cont_Y
              Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hY_sub]])
          hence "top1_continuous_map_on I_set I_top X TX f1" by (by100 simp)
          moreover have "f1 0 = p" "f1 1 = p"
            using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hf2X: "top1_is_loop_on X TX p f2"
        proof -
          have hf2_cont_Y: "top1_continuous_map_on I_set I_top ?Y ?TY f2"
            using hf2_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have "top1_continuous_map_on I_set I_top X TX (id \<circ> f2)"
            by (rule top1_continuous_map_on_comp[OF hf2_cont_Y
              Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hY_sub]])
          hence "top1_continuous_map_on I_set I_top X TX f2" by (by100 simp)
          moreover have "f2 0 = p" "f2 1 = p"
            using hf2_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have "top1_path_homotopic_on X TX p p f1 f2"
        proof -
          \<comment> \<open>f1 \\<in> ?incl c1: take f' = f1 (reflexive in ?Y), then id\\<circ>f1 = f1.\<close>
          have "f1 \<in> ?incl c1"
          proof -
            have "f1 \<in> {l. top1_loop_equiv_on ?Y ?TY p f1 l}"
              using top1_loop_equiv_on_refl[OF hf1_loop] by (by100 blast)
            moreover have "(\<lambda>x. x) \<circ> f1 = f1" by (by100 auto)
            hence "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f1) f1"
              using top1_loop_equiv_on_refl[OF hf1X] by (by100 simp)
            ultimately show ?thesis
              unfolding top1_fundamental_group_induced_on_def hc1_eq by (by100 blast)
          qed
          \<comment> \<open>Since ?incl c1 = ?incl c2: f1 \\<in> ?incl c2.\<close>
          hence "f1 \<in> ?incl c2" using heq by (by100 simp)
          \<comment> \<open>\\<exists>f'. loop\\_equiv(?Y, f2, f') \\<and> loop\\_equiv(X, f', f1).\<close>
          then obtain f' where hf'2: "top1_loop_equiv_on ?Y ?TY p f2 f'"
              and hf'1: "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') f1"
            unfolding top1_fundamental_group_induced_on_def hc2_eq by (by100 blast)
          have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
          have hf'1': "top1_loop_equiv_on X TX p f' f1" using hf'1 \<open>(\<lambda>x. x) \<circ> f' = f'\<close>
            by (by100 simp)
          \<comment> \<open>f2 ~ f' in ?Y, hence f2 ~ f' in X. Then f' ~ f1 in X. By transitivity: f2 ~ f1 in X.\<close>
          have "top1_loop_equiv_on X TX p f2 f'"
          proof -
            from hf'2[unfolded top1_loop_equiv_on_def]
            have "top1_path_homotopic_on ?Y ?TY p p f2 f'" by (by100 blast)
            from path_homotopic_subspace_to_ambient[OF hTX hY_sub _ this]
            have "top1_path_homotopic_on X TX p p f2 f'" by (by100 blast)
            have "top1_is_loop_on X TX p f'"
              using hf'1' unfolding top1_loop_equiv_on_def by (by100 blast)
            thus ?thesis unfolding top1_loop_equiv_on_def
              using hf2X \<open>top1_is_loop_on X TX p f'\<close>
                \<open>top1_path_homotopic_on X TX p p f2 f'\<close> by (by100 blast)
          qed
          from top1_loop_equiv_on_trans[OF hTX this hf'1']
          have "top1_loop_equiv_on X TX p f2 f1" .
          from top1_loop_equiv_on_sym[OF this]
          show "top1_path_homotopic_on X TX p p f1 f2"
            unfolding top1_loop_equiv_on_def by (by100 blast)
        qed
        \<comment> \<open>By hhtpy\\_finite, f1 ~ f2 in some \\<Union>F'.\<close>
        from hhtpy_finite[OF hf1X hf2X \<open>top1_path_homotopic_on X TX p p f1 f2\<close>]
        obtain F' where hF'fin: "finite F'" and hF'J: "F' \<subseteq> J"
            and hF'htpy: "top1_path_homotopic_on (\<Union>\<gamma>\<in>F'. C \<gamma>)
                (subspace_topology X TX (\<Union>\<gamma>\<in>F'. C \<gamma>)) p p f1 f2" by (by100 blast)
        let ?FF = "F \<union> F'"
        \<comment> \<open>f1 ~ f2 in \\<Union>?FF (lifting from \\<Union>F').\<close>
        have hF'_sub_FF: "(\<Union>\<gamma>\<in>F'. C \<gamma>) \<subseteq> (\<Union>\<gamma>\<in>?FF. C \<gamma>)" by (by100 blast)
        let ?YFF = "\<Union>\<gamma>\<in>?FF. C \<gamma>"
        let ?TYFF = "subspace_topology X TX ?YFF"
        have hYFF_sub: "?YFF \<subseteq> X" using hC hFJ hF'J by (by100 blast)
        have hTYFF: "is_topology_on ?YFF ?TYFF" by (rule subspace_topology_is_topology_on[OF hTX hYFF_sub])
        have hhtpy_FF: "top1_path_homotopic_on ?YFF ?TYFF p p f1 f2"
        proof -
          have "subspace_topology ?YFF ?TYFF (\<Union>\<gamma>\<in>F'. C \<gamma>) = subspace_topology X TX (\<Union>\<gamma>\<in>F'. C \<gamma>)"
            by (rule subspace_topology_trans) (use hF'_sub_FF in blast)
          from path_homotopic_subspace_to_ambient[OF hTYFF hF'_sub_FF this[symmetric] hF'htpy]
          show ?thesis .
        qed
        \<comment> \<open>f1 ~ f2 in ?YFF \\<Longrightarrow> [f1] = [f2] in \\<pi>\\_1(?YFF).
           The inclusion \\<pi>\\_1(?Y) \\<hookrightarrow> \\<pi>\\_1(?YFF) is injective (by free\\_group\\_hom\\_subset\\_injective).
           Since c1 = [f1]\\_{?Y} and c2 = [f2]\\_{?Y} map to the same class in \\<pi>\\_1(?YFF),
           and the map is injective, c1 = c2.\<close>
        \<comment> \<open>The inclusion \\<pi>\\_1(?Y) \\<hookrightarrow> \\<pi>\\_1(?YFF) is injective.
           This follows from free\\_group\\_hom\\_subset\\_injective applied to
           free(F) \\<hookrightarrow> free(F\\<union>F'), composed with the isos.\<close>
        \<comment> \<open>The inclusion \\<pi>\\_1(?Y) \\<hookrightarrow> \\<pi>\\_1(?YFF) is injective.\<close>
        let ?incl_FF = "top1_fundamental_group_induced_on ?Y ?TY p ?YFF ?TYFF p (\<lambda>x. x)"
        have hF_sub_FF: "?Y \<subseteq> ?YFF" by (by100 blast)
        have hpYFF: "p \<in> ?YFF" using hpY hF_sub_FF by (by100 blast)
        have hsubsp_eq: "subspace_topology ?YFF ?TYFF ?Y = ?TY"
          by (rule subspace_topology_trans) (use hF_sub_FF in blast)
        have hincl_FF_hom: "top1_group_hom_on
            (top1_fundamental_group_carrier ?Y ?TY p) (top1_fundamental_group_mul ?Y ?TY p)
            (top1_fundamental_group_carrier ?YFF ?TYFF p) (top1_fundamental_group_mul ?YFF ?TYFF p)
            ?incl_FF"
          using subspace_inclusion_induced_hom[OF hTYFF hF_sub_FF hpY]
            hsubsp_eq by (by100 simp)
        \<comment> \<open>?incl\\_FF(c1) = [f1]\\_{?YFF} and ?incl\\_FF(c2) = [f2]\\_{?YFF}.\<close>
        \<comment> \<open>From hhtpy\\_FF: f1 ~ f2 in ?YFF, so [f1] = [f2] in \\<pi>\\_1(?YFF).\<close>
        have hf1_loop_FF: "top1_is_loop_on ?YFF ?TYFF p f1"
        proof -
          have "top1_continuous_map_on I_set I_top ?Y ?TY f1"
            using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have hf1_cont_FF: "top1_continuous_map_on I_set I_top ?YFF ?TYFF f1"
          proof -
            have "f1 ` I_set \<subseteq> ?Y" using hf1_loop
              unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
              by (by100 blast)
            hence "f1 ` I_set \<subseteq> ?YFF" using hF_sub_FF by (by100 blast)
            have "top1_continuous_map_on I_set I_top X TX f1"
              using hf1X unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                rule_format] this \<open>f1 ` I_set \<subseteq> ?YFF\<close> hYFF_sub
            show ?thesis by (by100 blast)
          qed
          moreover have "f1 0 = p" "f1 1 = p"
            using hf1_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hf2_loop_FF: "top1_is_loop_on ?YFF ?TYFF p f2"
        proof -
          have "f2 ` I_set \<subseteq> ?Y" using hf2_loop
            unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
            by (by100 blast)
          hence "f2 ` I_set \<subseteq> ?YFF" using hF_sub_FF by (by100 blast)
          have "top1_continuous_map_on I_set I_top X TX f2"
            using hf2X unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
              rule_format] this \<open>f2 ` I_set \<subseteq> ?YFF\<close> hYFF_sub
          have "top1_continuous_map_on I_set I_top ?YFF ?TYFF f2" by (by100 blast)
          moreover have "f2 0 = p" "f2 1 = p"
            using hf2_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        qed
        have hloop_equiv_FF: "top1_loop_equiv_on ?YFF ?TYFF p f1 f2"
          unfolding top1_loop_equiv_on_def
          using hf1_loop_FF hf2_loop_FF hhtpy_FF by (by100 blast)
        \<comment> \<open>?incl\\_FF(c1) = ?incl\\_FF(c2) in \\<pi>\\_1(?YFF).\<close>
        have hincl_c1: "?incl_FF c1 = {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}"
          unfolding top1_fundamental_group_induced_on_def hc1_eq
        proof (rule set_eqI, rule iffI)
          fix h assume "h \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on ?Y ?TY p f1 g}.
              top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) g}"
          then obtain f' where hf': "top1_loop_equiv_on ?Y ?TY p f1 f'"
              "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
          have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
          have "top1_loop_equiv_on ?YFF ?TYFF p f' h" using hf'(2) \<open>_ = f'\<close> by (by100 simp)
          have "top1_loop_equiv_on ?YFF ?TYFF p f1 f'"
          proof -
            from hf'(1)[unfolded top1_loop_equiv_on_def]
            have "top1_path_homotopic_on ?Y ?TY p p f1 f'" by (by100 blast)
            have "subspace_topology ?YFF ?TYFF ?Y = ?TY" using hsubsp_eq by (by100 blast)
            from path_homotopic_subspace_to_ambient[OF hTYFF hF_sub_FF this[symmetric]
                \<open>top1_path_homotopic_on ?Y ?TY p p f1 f'\<close>]
            have "top1_path_homotopic_on ?YFF ?TYFF p p f1 f'" .
            have "top1_is_loop_on ?YFF ?TYFF p f'"
              using \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>
              unfolding top1_loop_equiv_on_def by (by100 blast)
            thus ?thesis unfolding top1_loop_equiv_on_def
              using hf1_loop_FF \<open>top1_path_homotopic_on ?YFF ?TYFF p p f1 f'\<close>
              by (by100 blast)
          qed
          from top1_loop_equiv_on_trans[OF hTYFF this \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>]
          show "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}" by (by100 blast)
        next
          fix h assume "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}"
          have "top1_loop_equiv_on ?Y ?TY p f1 f1" by (rule top1_loop_equiv_on_refl[OF hf1_loop])
          moreover have "(\<lambda>x. x) \<circ> f1 = f1" by (by100 auto)
          hence "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f1) h"
            using \<open>h \<in> _\<close> by (by100 simp)
          ultimately show "h \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on ?Y ?TY p f1 g}.
              top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) g}" by (by100 blast)
        qed
        moreover have hincl_c2: "?incl_FF c2 = {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}"
          unfolding top1_fundamental_group_induced_on_def hc2_eq
        proof (rule set_eqI, rule iffI)
          fix h assume "h \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on ?Y ?TY p f2 g}.
              top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) g}"
          then obtain f' where hf': "top1_loop_equiv_on ?Y ?TY p f2 f'"
              "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
          have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
          have "top1_loop_equiv_on ?YFF ?TYFF p f' h" using hf'(2) \<open>_ = f'\<close> by (by100 simp)
          have "top1_loop_equiv_on ?YFF ?TYFF p f2 f'"
          proof -
            from hf'(1)[unfolded top1_loop_equiv_on_def]
            have "top1_path_homotopic_on ?Y ?TY p p f2 f'" by (by100 blast)
            have "subspace_topology ?YFF ?TYFF ?Y = ?TY" using hsubsp_eq by (by100 blast)
            from path_homotopic_subspace_to_ambient[OF hTYFF hF_sub_FF this[symmetric]
                \<open>top1_path_homotopic_on ?Y ?TY p p f2 f'\<close>]
            have "top1_path_homotopic_on ?YFF ?TYFF p p f2 f'" .
            have "top1_is_loop_on ?YFF ?TYFF p f'"
              using \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>
              unfolding top1_loop_equiv_on_def by (by100 blast)
            thus ?thesis unfolding top1_loop_equiv_on_def
              using hf2_loop_FF \<open>top1_path_homotopic_on ?YFF ?TYFF p p f2 f'\<close>
              by (by100 blast)
          qed
          from top1_loop_equiv_on_trans[OF hTYFF this \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>]
          show "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}" by (by100 blast)
        next
          fix h assume "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}"
          have "top1_loop_equiv_on ?Y ?TY p f2 f2" by (rule top1_loop_equiv_on_refl[OF hf2_loop])
          moreover have "(\<lambda>x. x) \<circ> f2 = f2" by (by100 auto)
          hence "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f2) h"
            using \<open>h \<in> _\<close> by (by100 simp)
          ultimately show "h \<in> {g. \<exists>f\<in>{g. top1_loop_equiv_on ?Y ?TY p f2 g}.
              top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) g}" by (by100 blast)
        qed
        moreover have "{h. top1_loop_equiv_on ?YFF ?TYFF p f1 h} =
            {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}"
        proof (rule set_eqI, rule iffI)
          fix h assume "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}"
          hence "top1_loop_equiv_on ?YFF ?TYFF p f1 h" by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTYFF
              top1_loop_equiv_on_sym[OF hloop_equiv_FF] this]
          show "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}" by (by100 blast)
        next
          fix h assume "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f2 h}"
          hence "top1_loop_equiv_on ?YFF ?TYFF p f2 h" by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTYFF hloop_equiv_FF this]
          show "h \<in> {h. top1_loop_equiv_on ?YFF ?TYFF p f1 h}" by (by100 blast)
        qed
        ultimately have "?incl_FF c1 = ?incl_FF c2" by (by100 simp)
        \<comment> \<open>?incl\\_FF is injective (free group embedding).
           Both \\<pi>\\_1(?Y) and \\<pi>\\_1(?YFF) are free. The inclusion maps generators
           to generators. By free\\_group\\_hom\\_subset\\_injective: injective.\<close>
        moreover have "inj_on ?incl_FF (top1_fundamental_group_carrier ?Y ?TY p)"
        proof -
          \<comment> \<open>Get the free group for ?YFF.\<close>
          have hFFfin: "finite ?FF" using hFfin hF'fin by (by100 simp)
          have hFFJ: "?FF \<subseteq> J" using hFJ hF'J by (by100 blast)
          have hFFne: "?FF \<noteq> {}" using hFne by (by100 blast)
          from hfinite_free[OF hFFfin hFFJ hFFne]
          have hwedge_FF: "top1_is_wedge_of_circles_on ?YFF ?TYFF ?FF p" .
          have hg_FF: "\<forall>j\<in>?FF. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology ?YFF ?TYFF (C j)) (g j)"
          proof -
            { fix j assume "j \<in> ?FF"
              hence "j \<in> J" using hFFJ by (by100 blast)
              have "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
              moreover have "subspace_topology ?YFF ?TYFF (C j) = subspace_topology X TX (C j)"
                by (rule subspace_topology_trans) (use \<open>j \<in> ?FF\<close> in blast)
              ultimately have "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology ?YFF ?TYFF (C j)) (g j)" by (by100 simp) }
            thus ?thesis by (by100 blast)
          qed
          have hC_closed_FF: "\<forall>D\<subseteq>?YFF. closedin_on ?YFF ?TYFF D \<longleftrightarrow>
              (\<forall>j\<in>?FF. closedin_on (C j) (subspace_topology ?YFF ?TYFF (C j)) (C j \<inter> D))"
          proof (intro allI impI iffI)
            fix D assume hD: "D \<subseteq> ?YFF"
            from hcoh_sub[OF hFFJ, rule_format, OF hD]
            have hiff: "closedin_on ?YFF ?TYFF D \<longleftrightarrow>
                (\<forall>j\<in>?FF. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
            have htrans: "\<forall>j\<in>?FF. subspace_topology ?YFF ?TYFF (C j) = subspace_topology X TX (C j)"
              by (intro ballI, rule subspace_topology_trans) blast
            show "closedin_on ?YFF ?TYFF D \<Longrightarrow>
                \<forall>j\<in>?FF. closedin_on (C j) (subspace_topology ?YFF ?TYFF (C j)) (C j \<inter> D)"
              using hiff htrans by (by100 simp)
            show "(\<forall>j\<in>?FF. closedin_on (C j) (subspace_topology ?YFF ?TYFF (C j)) (C j \<inter> D)) \<Longrightarrow>
                closedin_on ?YFF ?TYFF D"
              using hiff htrans by (by100 simp)
          qed
          have hbase_FF: "\<forall>j\<in>?FF. g j (1, 0) = p" using hg hFFJ by (by100 blast)
          have hC_data_FF: "\<forall>j\<in>?FF. C j \<subseteq> ?YFF \<and> p \<in> C j" using hC hFFJ by (by100 blast)
          have hC_union_FF: "(\<Union>j\<in>?FF. C j) = ?YFF" by (by100 blast)
          have hC_disj_FF: "\<forall>i\<in>?FF. \<forall>j\<in>?FF. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
            using hdisjoint hFFJ by (by100 blast)
          from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge_FF hFFfin
              hg_FF hbase_FF hC_data_FF hC_union_FF hC_disj_FF hC_closed_FF]
          obtain GFF :: "int set" and mulFF eFF invgFF and \<eta>FF :: "'i \<Rightarrow> int" and \<Phi>FF
            where hfreeFF: "top1_is_free_group_full_on GFF mulFF eFF invgFF \<eta>FF ?FF"
              and hisoFF: "top1_group_iso_on GFF mulFF
                  (top1_fundamental_group_carrier ?YFF ?TYFF p)
                  (top1_fundamental_group_mul ?YFF ?TYFF p) \<Phi>FF"
              and hgensFF: "\<forall>j\<in>?FF. \<Phi>FF (\<eta>FF j) = {l. top1_loop_equiv_on ?YFF ?TYFF p
                  (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
            by (by100 blast)
          \<comment> \<open>The composition: \\<Phi>\\_FF\<inverse> \\<circ> incl\\_FF \\<circ> \\<Phi>\\_F: free(F) \\<rightarrow> free(F\\<union>F').
             This maps \\<eta>\\_F(\\<alpha>) to \\<eta>\\_FF(\\<alpha>) for \\<alpha> \\<in> F.
             By free\\_group\\_hom\\_subset\\_injective, it's injective.
             Since \\<Phi>\\_F, \\<Phi>\\_FF are bijections, incl\\_FF is injective.\<close>
          \<comment> \<open>For simplicity, we show injectivity directly:
             if incl\\_FF(c) = incl\\_FF(c') then c = c'.
             This was already handled by the enclosing proof structure (inj\\_onI).
             The injectivity follows from: if c \\<noteq> id, then incl\\_FF(c) \\<noteq> id
             (by free group embedding). Equivalently: ker(incl\\_FF) = {id}.\<close>
          \<comment> \<open>\\<Phi>\\_F and \\<Phi>\\_FF are available from chosen\\_loops\\_arb.\<close>
          have h\<Phi>F_bij: "bij_betw \<Phi>F GF (top1_fundamental_group_carrier ?Y ?TY p)"
            using hisoF unfolding top1_group_iso_on_def by (by100 blast)
          have h\<Phi>FF_bij: "bij_betw \<Phi>FF GFF (top1_fundamental_group_carrier ?YFF ?TYFF p)"
            using hisoFF unfolding top1_group_iso_on_def by (by100 blast)
          have h\<Phi>F_inj: "inj_on \<Phi>F GF"
            using h\<Phi>F_bij unfolding bij_betw_def by (by100 blast)
          have h\<Phi>FF_inj: "inj_on \<Phi>FF GFF"
            using h\<Phi>FF_bij unfolding bij_betw_def by (by100 blast)
          \<comment> \<open>Compose: \\<psi> = \\<Phi>\\_FF\<inverse> \\<circ> incl\\_FF \\<circ> \\<Phi>\\_F: GF \\<rightarrow> GFF.
             This is a hom mapping \\<eta>\\_F(\\<alpha>) to \\<eta>\\_FF(\\<alpha>) for \\<alpha> \\<in> F.
             By free\\_group\\_hom\\_subset\\_injective: \\<psi> is injective.
             Since \\<Phi>\\_F is bijective, incl\\_FF \\<circ> \\<Phi>\\_F is injective on GF.
             Since \\<Phi>\\_F is surjective onto \\<pi>\\_1(?Y), incl\\_FF is injective on \\<pi>\\_1(?Y).\<close>
          \<comment> \<open>Alternative direct argument: if incl\\_FF(c) = incl\\_FF(c'), then
             \\<Phi>\\_FF\<inverse>(incl\\_FF(c)) = \\<Phi>\\_FF\<inverse>(incl\\_FF(c')). The map \\<Phi>\\_FF\<inverse> \\<circ> incl\\_FF \\<circ> \\<Phi>\\_F
             is injective (free\\_group\\_hom\\_subset\\_injective). So \\<Phi>\\_F\<inverse>(c) = \\<Phi>\\_F\<inverse>(c').
             Since \\<Phi>\\_F bijective: c = c'.\<close>
          \<comment> \<open>By free\\_group\\_hom\\_exists + free\\_group\\_hom\\_subset\\_injective:
             the algebraic map \\<psi>: GF \\<rightarrow> GFF with \\<psi>(\\<eta>\\_F(\\<alpha>)) = \\<eta>\\_FF(\\<alpha>) is injective.
             Composing with the bijections \\<Phi>\\_F, \\<Phi>\\_FF gives incl\\_FF injective.
             This requires finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb to verify
             the generator correspondence \\<Phi>(\\<eta>(\\<alpha>)) = [gen\\_loop \\<alpha>].\<close>
          \<comment> \<open>Construct \\<psi>: GF \\<rightarrow> GFF with \\<psi>(\\<eta>\\_F(\\<alpha>)) = \\<eta>\\_FF(\\<alpha>) using free\\_group\\_hom\\_exists.\<close>
          have hGFF_grp: "top1_is_group_on GFF mulFF eFF invgFF"
            using hfreeFF unfolding top1_is_free_group_full_on_def by (by100 blast)
          have hGF_grp: "top1_is_group_on GF mulF eF invgF"
            using hfreeF unfolding top1_is_free_group_full_on_def by (by100 blast)
          have h\<eta>FF_in: "\<forall>\<alpha>\<in>F. \<eta>FF \<alpha> \<in> GFF"
            using hfreeFF unfolding top1_is_free_group_full_on_def by (by100 blast)
          from free_group_hom_exists[OF hfreeF hGFF_grp h\<eta>FF_in]
          obtain \<psi> where h\<psi>_hom: "top1_group_hom_on GF mulF GFF mulFF \<psi>"
              and h\<psi>_gen: "\<forall>\<alpha>\<in>F. \<psi> (\<eta>F \<alpha>) = \<eta>FF \<alpha>" by (by100 blast)
          \<comment> \<open>By free\\_group\\_hom\\_subset\\_injective: \\<psi> is injective.\<close>
          have hF_sub_FF: "F \<subseteq> ?FF" by (by100 blast)
          from free_group_hom_subset_injective[OF hfreeF hfreeFF hF_sub_FF h\<psi>_hom h\<psi>_gen]
          have h\<psi>_inj: "inj_on \<psi> GF" .
          \<comment> \<open>incl\\_FF = \\<Phi>\\_FF \\<circ> \\<psi> \\<circ> \\<Phi>\\_F\\<inverse> (on generators, by free\\_group\\_hom\\_unique).
             Since \\<psi> injective + \\<Phi>s bijective \\<Longrightarrow> incl\\_FF injective.\<close>
          \<comment> \<open>Simpler: show incl\\_FF injective directly.
             Take c, c' with incl\\_FF(c) = incl\\_FF(c').
             Let x = \\<Phi>\\_F\\<inverse>(c), y = \\<Phi>\\_F\\<inverse>(c'). Both in GF.
             \\<Phi>\\_FF(\\<psi>(x)) = incl\\_FF(\\<Phi>\\_F(x)) = incl\\_FF(c) = incl\\_FF(c') = \\<Phi>\\_FF(\\<psi>(y)).
             \\<Phi>\\_FF injective: \\<psi>(x) = \\<psi>(y).
             \\<psi> injective: x = y.
             \\<Phi>\\_F injective: c = c'.
             BUT: \\<Phi>\\_FF(\\<psi>(x)) = incl\\_FF(\\<Phi>\\_F(x)) requires that the composition agrees
             with the topological inclusion. This uses free\\_group\\_hom\\_unique.\<close>
          \<comment> \<open>Now show: for c \\<in> \\<pi>\\_1(?Y) with incl\\_FF(c) = incl\\_FF(c'),
             c = c'. Use: \\<Phi>\\_F\\<inverse>(c) = x \\<in> GF, \\<Phi>\\_F\\<inverse>(c') = y \\<in> GF.
             incl\\_FF(c) = incl\\_FF(\\<Phi>\\_F(x)), etc.
             Need: \\<Phi>\\_FF(\\<psi>(x)) = incl\\_FF(\\<Phi>\\_F(x)).
             Then \\<Phi>\\_FF(\\<psi>(x)) = \\<Phi>\\_FF(\\<psi>(y)) \\<Longrightarrow> \\<psi>(x) = \\<psi>(y) \\<Longrightarrow> x = y \\<Longrightarrow> c = c'.\<close>
          \<comment> \<open>The equality \\<Phi>\\_FF \\<circ> \\<psi> = incl\\_FF \\<circ> \\<Phi>\\_F on GF follows from
             free\\_group\\_hom\\_unique: both are homs GF \\<rightarrow> \\<pi>\\_1(?YFF)
             agreeing on generators \\<eta>\\_F(\\<alpha>).\<close>
          show ?thesis
          proof (rule inj_onI)
            fix c c' assume hcY: "c \<in> top1_fundamental_group_carrier ?Y ?TY p"
              and hc'Y: "c' \<in> top1_fundamental_group_carrier ?Y ?TY p"
              and hincl_eq: "?incl_FF c = ?incl_FF c'"
            \<comment> \<open>\\<Phi>\\_F is surjective onto \\<pi>\\_1(?Y). Get x, y.\<close>
            have hPhiF_surj: "\<Phi>F ` GF = top1_fundamental_group_carrier ?Y ?TY p"
              using h\<Phi>F_bij unfolding bij_betw_def by (by100 blast)
            from hcY obtain x where hxG: "x \<in> GF" and hcx: "c = \<Phi>F x"
              using hPhiF_surj by (by100 blast)
            from hc'Y obtain y where hyG: "y \<in> GF" and hc'y: "c' = \<Phi>F y"
              using hPhiF_surj by (by100 blast)
            \<comment> \<open>\\<Phi>\\_FF(\\<psi>(x)) = incl\\_FF(\\<Phi>\\_F(x)) (both homs agree on generators).\<close>
            \<comment> \<open>This requires free\\_group\\_hom\\_unique + generator correspondence.
               Both \\<Phi>\\_FF \\<circ> \\<psi> and incl\\_FF \\<circ> \\<Phi>\\_F are homs GF \\<rightarrow> \\<pi>\\_1(?YFF).
               They agree on generators \\<eta>\\_F(\\<alpha>):
               \\<Phi>\\_FF(\\<psi>(\\<eta>\\_F \\<alpha>)) = \\<Phi>\\_FF(\\<eta>\\_FF \\<alpha>) and
               incl\\_FF(\\<Phi>\\_F(\\<eta>\\_F \\<alpha>)) = incl\\_FF([gen\\_loop \\<alpha>]\\_{?Y}) = [gen\\_loop \\<alpha>]\\_{?YFF}
               and \\<Phi>\\_FF(\\<eta>\\_FF \\<alpha>) = [gen\\_loop \\<alpha>]\\_{?YFF}
               (from finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb).
               By free\\_group\\_hom\\_unique: they agree everywhere.\<close>
            have "?incl_FF (\<Phi>F x) = ?incl_FF (\<Phi>F y)"
              using hincl_eq hcx hc'y by (by100 simp)
            \<comment> \<open>Both equal \\<Phi>\\_FF(\\<psi>(x)) and \\<Phi>\\_FF(\\<psi>(y)) respectively (by the hom agreement).\<close>
            \<comment> \<open>So \\<Phi>\\_FF(\\<psi>(x)) = \\<Phi>\\_FF(\\<psi>(y)).\<close>
            have h\<psi>x_in: "\<psi> x \<in> GFF"
              using h\<psi>_hom hxG unfolding top1_group_hom_on_def by (by100 blast)
            have h\<psi>y_in: "\<psi> y \<in> GFF"
              using h\<psi>_hom hyG unfolding top1_group_hom_on_def by (by100 blast)
            \<comment> \<open>Both \\<Phi>\\_FF \\<circ> \\<psi> and incl\\_FF \\<circ> \\<Phi>\\_F are homs GF \\<rightarrow> \\<pi>\\_1(?YFF).
               They agree on all of GF by free\\_group\\_hom\\_unique.\<close>
            \<comment> \<open>Both homs agree on generators: for \\<alpha> \\<in> F,
               \\<Phi>\\_FF(\\<psi>(\\<eta>\\_F \\<alpha>)) = \\<Phi>\\_FF(\\<eta>\\_FF \\<alpha>) = [gen\\_loop \\<alpha>]\\_{?YFF}
               ?incl\\_FF(\\<Phi>\\_F(\\<eta>\\_F \\<alpha>)) = ?incl\\_FF([gen\\_loop \\<alpha>]\\_{?Y}) = [gen\\_loop \\<alpha>]\\_{?YFF}\<close>
            have hgen_agree: "\<forall>\<alpha>\<in>F. \<Phi>FF (\<psi> (\<eta>F \<alpha>)) = ?incl_FF (\<Phi>F (\<eta>F \<alpha>))"
            proof (intro ballI)
              fix \<alpha> assume h\<alpha>F: "\<alpha> \<in> F"
              have h\<alpha>J: "\<alpha> \<in> J" using h\<alpha>F hFJ by (by100 blast)
              have h\<alpha>FF: "\<alpha> \<in> ?FF" using h\<alpha>F by (by100 blast)
              \<comment> \<open>LHS: \\<Phi>\\_FF(\\<psi>(\\<eta>\\_F \\<alpha>)) = \\<Phi>\\_FF(\\<eta>\\_FF \\<alpha>) = [gen\\_loop \\<alpha>]\\_{?YFF}.\<close>
              have "\<psi> (\<eta>F \<alpha>) = \<eta>FF \<alpha>" using h\<psi>_gen h\<alpha>F by (by100 blast)
              hence hLHS: "\<Phi>FF (\<psi> (\<eta>F \<alpha>)) = \<Phi>FF (\<eta>FF \<alpha>)" by (by100 simp)
              have hPhiFF_gen: "\<Phi>FF (\<eta>FF \<alpha>) = {l. top1_loop_equiv_on ?YFF ?TYFF p
                  (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}"
                using hgensFF h\<alpha>FF by (by100 blast)
              \<comment> \<open>RHS: \\<Phi>\\_F(\\<eta>\\_F \\<alpha>) = [gen\\_loop \\<alpha>]\\_{?Y}.\<close>
              have hPhiF_gen: "\<Phi>F (\<eta>F \<alpha>) = {l. top1_loop_equiv_on ?Y ?TY p
                  (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}"
                using hgensF h\<alpha>F by (by100 blast)
              \<comment> \<open>?incl\\_FF([gen\\_loop \\<alpha>]\\_{?Y}) = [gen\\_loop \\<alpha>]\\_{?YFF}.\<close>
              have hincl_gen: "?incl_FF (\<Phi>F (\<eta>F \<alpha>)) = {l. top1_loop_equiv_on ?YFF ?TYFF p
                  (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}"
                unfolding hPhiF_gen top1_fundamental_group_induced_on_def
              proof (rule set_eqI, rule iffI)
                let ?gl = "\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))"
                fix h assume "h \<in> {ga. \<exists>f\<in>{l. top1_loop_equiv_on ?Y ?TY p ?gl l}.
                    top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) ga}"
                then obtain f' where hf'Y: "top1_loop_equiv_on ?Y ?TY p ?gl f'"
                    and hf'h: "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
                have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
                have "top1_loop_equiv_on ?YFF ?TYFF p f' h" using hf'h \<open>_ = f'\<close> by (by100 simp)
                have "top1_loop_equiv_on ?YFF ?TYFF p ?gl f'"
                proof -
                  from hf'Y[unfolded top1_loop_equiv_on_def]
                  have "top1_path_homotopic_on ?Y ?TY p p ?gl f'" by (by100 blast)
                  have hsubsp: "subspace_topology ?YFF ?TYFF ?Y = ?TY"
                    by (rule subspace_topology_trans) (use hF_sub_FF in blast)
                  have "top1_path_homotopic_on ?YFF ?TYFF p p ?gl f'"
                  proof -
                    from \<open>top1_path_homotopic_on ?Y ?TY p p ?gl f'\<close>[unfolded top1_path_homotopic_on_def]
                    obtain H_loc where
                        "top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H_loc"
                        "\<forall>s\<in>I_set. H_loc (s, 0) = ?gl s" "\<forall>s\<in>I_set. H_loc (s, 1) = f' s"
                        "\<forall>t\<in>I_set. H_loc (0, t) = p" "\<forall>t\<in>I_set. H_loc (1, t) = p"
                      by (by100 blast)
                    \<comment> \<open>H\\_loc: I\\<times>I \\<rightarrow> ?Y continuous. Lift to ?YFF via ?Y \\<subseteq> ?YFF \\<subseteq> X.\<close>
                    have hH_sub: "H_loc ` (I_set \<times> I_set) \<subseteq> ?Y"
                      using \<open>top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H_loc\<close>
                      unfolding top1_continuous_map_on_def by (by100 blast)
                    have hY_sub_YFF: "?Y \<subseteq> ?YFF" by (by100 blast)
                    have "H_loc ` (I_set \<times> I_set) \<subseteq> ?YFF"
                      using subset_trans[OF hH_sub hY_sub_YFF] .
                    \<comment> \<open>H\\_loc continuous into X.\<close>
                    have hII_top: "is_topology_on (I_set \<times> I_set) II_topology"
                      unfolding II_topology_def
                      using product_topology_on_is_topology_on[OF
                        top1_unit_interval_topology_is_topology_on
                        top1_unit_interval_topology_is_topology_on] .
                    have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (id \<circ> H_loc)"
                      by (rule top1_continuous_map_on_comp[OF
                        \<open>top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H_loc\<close>
                        Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hY_sub]])
                    hence "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX H_loc"
                      by (by100 simp)
                    \<comment> \<open>Restrict range to ?YFF.\<close>
                    from Theorem_18_2(5)[OF hII_top hTX hTX, rule_format]
                      this \<open>H_loc ` (I_set \<times> I_set) \<subseteq> ?YFF\<close> hYFF_sub
                    have "top1_continuous_map_on (I_set \<times> I_set) II_topology ?YFF ?TYFF H_loc"
                      by (by100 blast)
                    \<comment> \<open>?gl and f' are loops/paths in ?YFF.\<close>
                    have hf'_loop_YFF: "top1_is_loop_on ?YFF ?TYFF p f'"
                      using \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>
                      unfolding top1_loop_equiv_on_def by (by100 blast)
                    have hgl_loop_YFF: "top1_is_loop_on ?YFF ?TYFF p ?gl"
                    proof -
                      have "top1_is_loop_on X TX p ?gl"
                        using hgen h\<alpha>J unfolding gen_loop_def by (by100 blast)
                      have "?gl ` I_set \<subseteq> ?YFF"
                        using hgen h\<alpha>J h\<alpha>FF unfolding gen_loop_def by (by100 blast)
                      from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                          rule_format] \<open>top1_is_loop_on X TX p ?gl\<close> \<open>?gl ` I_set \<subseteq> ?YFF\<close> hYFF_sub
                      have "top1_continuous_map_on I_set I_top ?YFF ?TYFF ?gl"
                        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                      moreover have "?gl 0 = p" "?gl 1 = p"
                        using \<open>top1_is_loop_on X TX p ?gl\<close>
                        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                      ultimately show ?thesis
                        unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                    qed
                    show ?thesis
                      unfolding top1_path_homotopic_on_def
                      using \<open>top1_continuous_map_on (I_set \<times> I_set) II_topology ?YFF ?TYFF H_loc\<close>
                        \<open>\<forall>s\<in>I_set. H_loc (s, 0) = ?gl s\<close> \<open>\<forall>s\<in>I_set. H_loc (s, 1) = f' s\<close>
                        \<open>\<forall>t\<in>I_set. H_loc (0, t) = p\<close> \<open>\<forall>t\<in>I_set. H_loc (1, t) = p\<close>
                        hgl_loop_YFF hf'_loop_YFF
                      unfolding top1_is_loop_on_def by (by100 blast)
                  qed
                  have "top1_is_loop_on ?YFF ?TYFF p f'"
                    using \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>
                    unfolding top1_loop_equiv_on_def by (by100 blast)
                  have "top1_is_loop_on ?YFF ?TYFF p ?gl"
                  proof -
                    have "top1_is_loop_on X TX p ?gl"
                      using hgen h\<alpha>J unfolding gen_loop_def by (by100 blast)
                    have "?gl ` I_set \<subseteq> ?YFF"
                      using hgen h\<alpha>J h\<alpha>FF unfolding gen_loop_def by (by100 blast)
                    from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                        rule_format] \<open>top1_is_loop_on X TX p ?gl\<close> \<open>?gl ` I_set \<subseteq> ?YFF\<close> hYFF_sub
                    have "top1_continuous_map_on I_set I_top ?YFF ?TYFF ?gl"
                      unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                    moreover have "?gl 0 = p" "?gl 1 = p"
                      using \<open>top1_is_loop_on X TX p ?gl\<close>
                      unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                    ultimately show ?thesis
                      unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  qed
                  thus ?thesis unfolding top1_loop_equiv_on_def
                    using \<open>top1_is_loop_on ?YFF ?TYFF p f'\<close>
                      \<open>top1_path_homotopic_on ?YFF ?TYFF p p ?gl f'\<close> by (by100 blast)
                qed
                from top1_loop_equiv_on_trans[OF hTYFF this
                    \<open>top1_loop_equiv_on ?YFF ?TYFF p f' h\<close>]
                show "h \<in> {l. top1_loop_equiv_on ?YFF ?TYFF p ?gl l}" by (by100 blast)
              next
                let ?gl = "\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))"
                fix h assume "h \<in> {l. top1_loop_equiv_on ?YFF ?TYFF p ?gl l}"
                have "top1_is_loop_on ?Y ?TY p ?gl"
                proof -
                  have "top1_is_loop_on X TX p ?gl"
                    using hgen h\<alpha>J unfolding gen_loop_def by (by100 blast)
                  have "?gl ` I_set \<subseteq> ?Y"
                    using hgen h\<alpha>J h\<alpha>F unfolding gen_loop_def by (by100 blast)
                  from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                      rule_format] \<open>top1_is_loop_on X TX p ?gl\<close> \<open>?gl ` I_set \<subseteq> ?Y\<close> hY_sub
                  have "top1_continuous_map_on I_set I_top ?Y ?TY ?gl"
                    unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  moreover have "?gl 0 = p" "?gl 1 = p"
                    using \<open>top1_is_loop_on X TX p ?gl\<close>
                    unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                  ultimately show ?thesis
                    unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                qed
                from top1_loop_equiv_on_refl[OF this]
                have "?gl \<in> {l. top1_loop_equiv_on ?Y ?TY p ?gl l}" by (by100 blast)
                moreover have "(\<lambda>x. x) \<circ> ?gl = ?gl" by (by100 auto)
                hence "top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> ?gl) h"
                  using \<open>h \<in> _\<close> by (by100 simp)
                ultimately show "h \<in> {ga. \<exists>f\<in>{l. top1_loop_equiv_on ?Y ?TY p ?gl l}.
                    top1_loop_equiv_on ?YFF ?TYFF p ((\<lambda>x. x) \<circ> f) ga}" by (by100 blast)
              qed
              show "\<Phi>FF (\<psi> (\<eta>F \<alpha>)) = ?incl_FF (\<Phi>F (\<eta>F \<alpha>))"
                using hLHS hPhiFF_gen hincl_gen by (by100 simp)
            qed
            \<comment> \<open>By free\\_group\\_hom\\_unique: both homs agree on all of GF.\<close>
            have hpi1YFF_grp: "top1_is_group_on
                (top1_fundamental_group_carrier ?YFF ?TYFF p)
                (top1_fundamental_group_mul ?YFF ?TYFF p)
                (top1_fundamental_group_id ?YFF ?TYFF p)
                (top1_fundamental_group_invg ?YFF ?TYFF p)"
              by (rule top1_fundamental_group_is_group[OF hTYFF hpYFF])
            have hGF_gen: "GF = top1_subgroup_generated_on GF mulF eF invgF (\<eta>F ` F)"
              using hfreeF unfolding top1_is_free_group_full_on_def by (by100 blast)
            have h\<eta>F_in: "\<forall>s\<in>F. \<eta>F s \<in> GF"
              using hfreeF unfolding top1_is_free_group_full_on_def by (by100 blast)
            have h\<Phi>FF_hom: "top1_group_hom_on GFF mulFF
                (top1_fundamental_group_carrier ?YFF ?TYFF p)
                (top1_fundamental_group_mul ?YFF ?TYFF p) \<Phi>FF"
              using hisoFF unfolding top1_group_iso_on_def by (by100 blast)
            have h\<Phi>F_hom: "top1_group_hom_on GF mulF
                (top1_fundamental_group_carrier ?Y ?TY p)
                (top1_fundamental_group_mul ?Y ?TY p) \<Phi>F"
              using hisoF unfolding top1_group_iso_on_def by (by100 blast)
            have hcomp1_hom: "top1_group_hom_on GF mulF
                (top1_fundamental_group_carrier ?YFF ?TYFF p)
                (top1_fundamental_group_mul ?YFF ?TYFF p) (\<lambda>z. \<Phi>FF (\<psi> z))"
            proof -
              from group_hom_comp[OF h\<psi>_hom h\<Phi>FF_hom]
              have "top1_group_hom_on GF mulF
                  (top1_fundamental_group_carrier ?YFF ?TYFF p)
                  (top1_fundamental_group_mul ?YFF ?TYFF p) (\<Phi>FF \<circ> \<psi>)" .
              moreover have "(\<Phi>FF \<circ> \<psi>) = (\<lambda>z. \<Phi>FF (\<psi> z))" by (by100 auto)
              ultimately show ?thesis by (by100 simp)
            qed
            have hcomp2_hom: "top1_group_hom_on GF mulF
                (top1_fundamental_group_carrier ?YFF ?TYFF p)
                (top1_fundamental_group_mul ?YFF ?TYFF p) (\<lambda>z. ?incl_FF (\<Phi>F z))"
            proof -
              from group_hom_comp[OF h\<Phi>F_hom hincl_FF_hom]
              have "top1_group_hom_on GF mulF
                  (top1_fundamental_group_carrier ?YFF ?TYFF p)
                  (top1_fundamental_group_mul ?YFF ?TYFF p) (?incl_FF \<circ> \<Phi>F)" .
              moreover have "(?incl_FF \<circ> \<Phi>F) = (\<lambda>z. ?incl_FF (\<Phi>F z))" by (by100 auto)
              ultimately show ?thesis by (by100 simp)
            qed
            have hcomp_agree: "\<forall>z\<in>GF. \<Phi>FF (\<psi> z) = ?incl_FF (\<Phi>F z)"
              using free_group_hom_unique[OF hGF_grp hpi1YFF_grp hGF_gen h\<eta>F_in
                  hcomp1_hom hcomp2_hom hgen_agree] by (by100 blast)
            have hcomp_x: "\<Phi>FF (\<psi> x) = ?incl_FF (\<Phi>F x)"
              using hcomp_agree hxG by (by100 blast)
            have hcomp_y: "\<Phi>FF (\<psi> y) = ?incl_FF (\<Phi>F y)"
              using hcomp_agree hyG by (by100 blast)
            hence "\<Phi>FF (\<psi> x) = \<Phi>FF (\<psi> y)"
              using hcomp_x \<open>?incl_FF (\<Phi>F x) = ?incl_FF (\<Phi>F y)\<close> by (by100 simp)
            hence "\<psi> x = \<psi> y"
              using h\<Phi>FF_inj h\<psi>x_in h\<psi>y_in unfolding inj_on_def by (by100 blast)
            hence "x = y" using h\<psi>_inj hxG hyG unfolding inj_on_def by (by100 blast)
            thus "c = c'" using hcx hc'y by (by100 simp)
          qed
        qed
        ultimately show "c1 = c2" using hc1 hc2 unfolding inj_on_def by (by100 blast)
      qed
    qed
    define \<iota> where "\<iota> \<alpha> = {f. top1_loop_equiv_on X TX p (gen_loop \<alpha>) f}" for \<alpha>
    \<comment> \<open>Step 3: verify top1\\_is\\_free\\_group\\_full\\_on.\<close>
    show ?thesis
      unfolding top1_is_free_group_full_on_def
    proof (intro exI[of _ \<iota>] conjI)
      show "top1_is_group_on
          (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
          (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)"
        by (rule top1_fundamental_group_is_group[OF hTX hp])
      show "\<forall>s\<in>J. \<iota> s \<in> top1_fundamental_group_carrier X TX p"
      proof (intro ballI)
        fix s assume "s \<in> J"
        have "top1_is_loop_on X TX p (gen_loop s)" using hgen \<open>s \<in> J\<close> by (by100 blast)
        thus "\<iota> s \<in> top1_fundamental_group_carrier X TX p"
          unfolding \<iota>_def top1_fundamental_group_carrier_def by (by100 blast)
      qed
      show "inj_on \<iota> J"
      proof (rule inj_onI)
        fix \<alpha> \<beta> assume h\<alpha>J: "\<alpha> \<in> J" and h\<beta>J: "\<beta> \<in> J" and heq: "\<iota> \<alpha> = \<iota> \<beta>"
        \<comment> \<open>\\<iota>(\\<alpha>) = \\<iota>(\\<beta>) means gen\\_loop \\<alpha> \\<sim> gen\\_loop \\<beta> in X.\<close>
        have hloop_\<alpha>: "top1_is_loop_on X TX p (gen_loop \<alpha>)" using hgen h\<alpha>J by (by100 blast)
        have hloop_\<beta>: "top1_is_loop_on X TX p (gen_loop \<beta>)" using hgen h\<beta>J by (by100 blast)
        \<comment> \<open>From \\<iota>(\\<alpha>) = \\<iota>(\\<beta>), derive path homotopy.\<close>
        have hhtpy: "top1_path_homotopic_on X TX p p (gen_loop \<alpha>) (gen_loop \<beta>)"
        proof -
          from heq have "{f. top1_loop_equiv_on X TX p (gen_loop \<alpha>) f} =
              {f. top1_loop_equiv_on X TX p (gen_loop \<beta>) f}" unfolding \<iota>_def .
          hence "gen_loop \<beta> \<in> {f. top1_loop_equiv_on X TX p (gen_loop \<alpha>) f}"
          proof -
            have "gen_loop \<beta> \<in> {f. top1_loop_equiv_on X TX p (gen_loop \<beta>) f}"
              using top1_loop_equiv_on_refl[OF hloop_\<beta>] by (by100 blast)
            thus ?thesis using \<open>{f. top1_loop_equiv_on X TX p (gen_loop \<alpha>) f} =
                {f. top1_loop_equiv_on X TX p (gen_loop \<beta>) f}\<close> by (by100 blast)
          qed
          hence "top1_loop_equiv_on X TX p (gen_loop \<alpha>) (gen_loop \<beta>)" by (by100 blast)
          thus ?thesis unfolding top1_loop_equiv_on_def top1_is_loop_on_def by (by100 blast)
        qed
        \<comment> \<open>By hhtpy\\_finite, the homotopy lies in a finite sub-wedge.\<close>
        from hhtpy_finite[OF hloop_\<alpha> hloop_\<beta> hhtpy]
        obtain F' where hF'fin: "finite F'" and hF'J: "F' \<subseteq> J"
          and hF'htpy: "top1_path_homotopic_on (\<Union>\<gamma>\<in>F'. C \<gamma>)
              (subspace_topology X TX (\<Union>\<gamma>\<in>F'. C \<gamma>)) p p (gen_loop \<alpha>) (gen_loop \<beta>)"
          by (by100 blast)
        \<comment> \<open>Take F = {\\<alpha>, \\<beta>} \\<union> F'. Both gen\\_loops and the homotopy lie in \\<Union>F.\<close>
        let ?F = "{\<alpha>, \<beta>} \<union> F'"
        have hFfin: "finite ?F" using hF'fin by (by100 simp)
        have hFJ: "?F \<subseteq> J" using h\<alpha>J h\<beta>J hF'J by (by100 blast)
        have hFne: "?F \<noteq> {}" by (by100 blast)
        \<comment> \<open>gen\\_loop \\<alpha> and gen\\_loop \\<beta> are homotopic in \\<Union>?F (lift from \\<Union>F').\<close>
        have hF'_sub_F: "(\<Union>\<gamma>\<in>F'. C \<gamma>) \<subseteq> (\<Union>\<gamma>\<in>?F. C \<gamma>)" by (by100 blast)
        have hF_sub_X: "(\<Union>\<gamma>\<in>?F. C \<gamma>) \<subseteq> X" using hC hFJ by (by100 blast)
        \<comment> \<open>Subspace topology of \\<Union>F' in \\<Union>?F = subspace topology in X (transitivity).\<close>
        have hsubsp_eq: "subspace_topology X TX (\<Union>\<gamma>\<in>F'. C \<gamma>) =
            subspace_topology (\<Union>\<gamma>\<in>?F. C \<gamma>) (subspace_topology X TX (\<Union>\<gamma>\<in>?F. C \<gamma>))
                (\<Union>\<gamma>\<in>F'. C \<gamma>)"
          by (rule subspace_topology_trans[symmetric]) (use hF'_sub_F in blast)
        have hhtpy_F: "top1_path_homotopic_on (\<Union>\<gamma>\<in>?F. C \<gamma>)
            (subspace_topology X TX (\<Union>\<gamma>\<in>?F. C \<gamma>)) p p (gen_loop \<alpha>) (gen_loop \<beta>)"
        proof -
          have hTF: "is_topology_on (\<Union>\<gamma>\<in>?F. C \<gamma>) (subspace_topology X TX (\<Union>\<gamma>\<in>?F. C \<gamma>))"
            by (rule subspace_topology_is_topology_on[OF hTX hF_sub_X])
          from path_homotopic_subspace_to_ambient[OF hTF hF'_sub_F hsubsp_eq hF'htpy]
          show ?thesis .
        qed
        \<comment> \<open>The sub-wedge \\<Union>?F is a wedge with free \\<pi>\\_1.\<close>
        from hfinite_free[OF hFfin hFJ hFne]
        have hwedge_F: "top1_is_wedge_of_circles_on (\<Union>\<gamma>\<in>?F. C \<gamma>)
            (subspace_topology X TX (\<Union>\<gamma>\<in>?F. C \<gamma>)) ?F p" .
        \<comment> \<open>In \\<pi>\\_1(\\<Union>?F), gen\\_loop \\<alpha> and gen\\_loop \\<beta> are generators indexed by \\<alpha> and \\<beta>.
           If \\<alpha> \\<noteq> \\<beta>, they generate distinct elements (injectivity of free generators).
           But they are homotopic in \\<Union>?F, contradiction.\<close>
        \<comment> \<open>Apply finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb to \\<Union>?F.\<close>
        let ?Y = "\<Union>\<gamma>\<in>?F. C \<gamma>"
        let ?TY = "subspace_topology X TX ?Y"
        have hg_F: "\<forall>j\<in>?F. top1_homeomorphism_on top1_S1 top1_S1_topology
            (C j) (subspace_topology ?Y ?TY (C j)) (g j)"
        proof -
          {
            fix j assume hjF: "j \<in> ?F"
            hence "j \<in> J" using hFJ by (by100 blast)
            have hgj: "top1_homeomorphism_on top1_S1 top1_S1_topology
                (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
            have "subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
              by (rule subspace_topology_trans) (use hjF in blast)
            hence "top1_homeomorphism_on top1_S1 top1_S1_topology
                (C j) (subspace_topology ?Y ?TY (C j)) (g j)"
              using hgj by (by100 simp)
          }
          thus ?thesis by (by100 blast)
        qed
        have hC_closed_F: "\<forall>D\<subseteq>?Y. closedin_on ?Y ?TY D \<longleftrightarrow>
            (\<forall>j\<in>?F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D))"
        proof (intro allI impI iffI)
          fix D assume hD: "D \<subseteq> ?Y"
          from hcoh_sub[OF hFJ, rule_format, OF hD]
          have hiff: "closedin_on ?Y ?TY D \<longleftrightarrow>
              (\<forall>j\<in>?F. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
          have htrans: "\<forall>j\<in>?F. subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
          proof (intro ballI)
            fix j assume "j \<in> ?F"
            show "subspace_topology ?Y ?TY (C j) = subspace_topology X TX (C j)"
              by (rule subspace_topology_trans) (use \<open>j \<in> ?F\<close> in blast)
          qed
          show "closedin_on ?Y ?TY D \<Longrightarrow>
              \<forall>j\<in>?F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D)"
            using hiff htrans by (by100 simp)
          show "(\<forall>j\<in>?F. closedin_on (C j) (subspace_topology ?Y ?TY (C j)) (C j \<inter> D)) \<Longrightarrow>
              closedin_on ?Y ?TY D"
            using hiff htrans by (by100 simp)
        qed
        have hbase_F: "\<forall>j\<in>?F. g j (1, 0) = p"
          using hg hFJ by (by100 blast)
        have hC_data_F: "\<forall>j\<in>?F. C j \<subseteq> ?Y \<and> p \<in> C j"
          using hC hFJ by (by100 blast)
        have hC_union_F: "(\<Union>j\<in>?F. C j) = ?Y" by (by100 blast)
        have hC_disj_F: "\<forall>i\<in>?F. \<forall>j\<in>?F. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
          using hdisjoint hFJ by (by100 blast)
        from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge_F hFfin
            hg_F hbase_F hC_data_F hC_union_F hC_disj_F hC_closed_F]
        obtain F_grp :: "int set" and mul_F e_F invg_F and \<eta>_F :: "'i \<Rightarrow> int" and \<Phi>_F
          where hfree_F: "top1_is_free_group_full_on F_grp mul_F e_F invg_F \<eta>_F ?F"
            and hiso_F: "top1_group_iso_on F_grp mul_F
                (top1_fundamental_group_carrier ?Y ?TY p)
                (top1_fundamental_group_mul ?Y ?TY p) \<Phi>_F"
            and hgens_F: "\<forall>j\<in>?F. \<Phi>_F (\<eta>_F j) = {l. top1_loop_equiv_on ?Y ?TY p
                (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
          by (by100 blast)
        \<comment> \<open>gen\\_loop j t = g j (cos(2\\<pi>t), sin(2\\<pi>t)).\<close>
        have hPhi_\<alpha>: "\<Phi>_F (\<eta>_F \<alpha>) = {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l}"
        proof -
          have "\<alpha> \<in> ?F" by (by100 blast)
          from hgens_F[rule_format, OF this]
          show ?thesis unfolding gen_loop_def by (by100 blast)
        qed
        have hPhi_\<beta>: "\<Phi>_F (\<eta>_F \<beta>) = {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l}"
        proof -
          have "\<beta> \<in> ?F" by (by100 blast)
          from hgens_F[rule_format, OF this]
          show ?thesis unfolding gen_loop_def by (by100 blast)
        qed
        \<comment> \<open>gen\\_loop \\<alpha> \\<sim> gen\\_loop \\<beta> in ?Y, so their loop classes coincide.\<close>
        have hloop_eq: "top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) (gen_loop \<beta>)"
          using hhtpy_F unfolding top1_loop_equiv_on_def top1_is_loop_on_def
            top1_path_homotopic_on_def by (by100 blast)
        have hTY: "is_topology_on ?Y ?TY"
          by (rule subspace_topology_is_topology_on[OF hTX hF_sub_X])
        have hclass_eq: "{l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l} =
            {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l}"
        proof (rule set_eqI, rule iffI)
          fix l assume "l \<in> {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l}"
          hence "top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l" by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTY
              top1_loop_equiv_on_sym[OF hloop_eq] this]
          show "l \<in> {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l}" by (by100 blast)
        next
          fix l assume "l \<in> {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l}"
          hence "top1_loop_equiv_on ?Y ?TY p (gen_loop \<beta>) l" by (by100 blast)
          from top1_loop_equiv_on_trans[OF hTY hloop_eq this]
          show "l \<in> {l. top1_loop_equiv_on ?Y ?TY p (gen_loop \<alpha>) l}" by (by100 blast)
        qed
        hence "\<Phi>_F (\<eta>_F \<alpha>) = \<Phi>_F (\<eta>_F \<beta>)" using hPhi_\<alpha> hPhi_\<beta> by (by100 simp)
        \<comment> \<open>\\<Phi>\\_F is injective (iso), so \\<eta>\\_F \\<alpha> = \\<eta>\\_F \\<beta>.\<close>
        hence h\<eta>_eq: "\<eta>_F \<alpha> = \<eta>_F \<beta>"
        proof -
          assume hPhi_eq: "\<Phi>_F (\<eta>_F \<alpha>) = \<Phi>_F (\<eta>_F \<beta>)"
          have h\<alpha>F: "\<eta>_F \<alpha> \<in> F_grp"
            using hfree_F unfolding top1_is_free_group_full_on_def by (by100 blast)
          have h\<beta>F: "\<eta>_F \<beta> \<in> F_grp"
            using hfree_F unfolding top1_is_free_group_full_on_def by (by100 blast)
          have "inj_on \<Phi>_F F_grp"
            using hiso_F unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
          thus ?thesis using hPhi_eq h\<alpha>F h\<beta>F unfolding inj_on_def by (by100 blast)
        qed
        \<comment> \<open>\\<eta>\\_F is injective on ?F (free group condition).\<close>
        have "inj_on \<eta>_F ?F"
          using hfree_F unfolding top1_is_free_group_full_on_def by (by100 blast)
        thus "\<alpha> = \<beta>"
          using h\<eta>_eq unfolding inj_on_def by (by100 blast)
      qed
      show "top1_fundamental_group_carrier X TX p =
          top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
              (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
      proof (rule set_eqI, rule iffI)
        fix c assume hc: "c \<in> top1_fundamental_group_carrier X TX p"
        \<comment> \<open>c = [f] for some loop f. By hloop\\_finite, f lies in a finite sub-wedge.\<close>
        from hc[unfolded top1_fundamental_group_carrier_def]
        obtain f where hf: "top1_is_loop_on X TX p f" and hc_eq: "c = {g. top1_loop_equiv_on X TX p f g}"
          by (by100 blast)
        from hloop_finite[OF hf] obtain F where hFfin: "finite F" and hFJ: "F \<subseteq> J"
            and hf_in_F: "f ` top1_unit_interval \<subseteq> (\<Union>\<alpha>\<in>F. C \<alpha>)" by (by100 blast)
        \<comment> \<open>Ensure F is non-empty (add an arbitrary element from J if needed).\<close>
        have "J \<noteq> {}" using hp hcover by (by100 blast)
        then obtain \<gamma> where "\<gamma> \<in> J" by (by100 blast)
        let ?F2 = "F \<union> {\<gamma>}"
        have hF2fin: "finite ?F2" using hFfin by (by100 simp)
        have hF2J: "?F2 \<subseteq> J" using hFJ \<open>\<gamma> \<in> J\<close> by (by100 blast)
        have hF2ne: "?F2 \<noteq> {}" by (by100 blast)
        \<comment> \<open>[f] is in the image of the inclusion \\<pi>\\_1(\\<Union>?F) \\<rightarrow> \\<pi>\\_1(X).
           In \\<pi>\\_1(\\<Union>?F), every element is a product of generators [gen\\_loop \\<alpha>].
           The inclusion sends these to \\<iota>(\\<alpha>). So c \\<in> subgroup\\_generated.\<close>
        show "c \<in> top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
            (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
            (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
        proof -
          let ?Y2 = "\<Union>\<alpha>\<in>?F2. C \<alpha>"
          let ?TY2 = "subspace_topology X TX ?Y2"
          have hY2_sub: "?Y2 \<subseteq> X" using hC hF2J by (by100 blast)
          have hpY2: "p \<in> ?Y2" using hC \<open>\<gamma> \<in> J\<close> by (by100 blast)
          have hTY2: "is_topology_on ?Y2 ?TY2"
            by (rule subspace_topology_is_topology_on[OF hTX hY2_sub])
          \<comment> \<open>Step 1: \\<Union>?F2 is a wedge. Apply finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb.\<close>
          from hfinite_free[OF hF2fin hF2J hF2ne]
          have hwedge2: "top1_is_wedge_of_circles_on ?Y2 ?TY2 ?F2 p" .
          \<comment> \<open>Prepare homeomorphisms for the sub-wedge.\<close>
          have hg_F2: "\<forall>j\<in>?F2. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology ?Y2 ?TY2 (C j)) (g j)"
          proof -
            {
              fix j assume hjF: "j \<in> ?F2"
              hence "j \<in> J" using hF2J by (by100 blast)
              have hgj: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
              have "subspace_topology ?Y2 ?TY2 (C j) = subspace_topology X TX (C j)"
                by (rule subspace_topology_trans) (use hjF in blast)
              hence "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology ?Y2 ?TY2 (C j)) (g j)"
                using hgj by (by100 simp)
            }
            thus ?thesis by (by100 blast)
          qed
          have hbase_F2: "\<forall>j\<in>?F2. g j (1, 0) = p" using hg hF2J by (by100 blast)
          have hC_data_F2: "\<forall>j\<in>?F2. C j \<subseteq> ?Y2 \<and> p \<in> C j" using hC hF2J by (by100 blast)
          have hC_union_F2: "(\<Union>j\<in>?F2. C j) = ?Y2" by (by100 blast)
          have hC_disj_F2: "\<forall>i\<in>?F2. \<forall>j\<in>?F2. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
            using hdisjoint hF2J by (by100 blast)
          have hC_closed_F2: "\<forall>D\<subseteq>?Y2. closedin_on ?Y2 ?TY2 D \<longleftrightarrow>
              (\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D))"
          proof (intro allI impI iffI)
            fix D assume hD: "D \<subseteq> ?Y2"
            from hcoh_sub[OF hF2J, rule_format, OF hD]
            have hiff: "closedin_on ?Y2 ?TY2 D \<longleftrightarrow>
                (\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
            have htrans: "\<forall>j\<in>?F2. subspace_topology ?Y2 ?TY2 (C j) = subspace_topology X TX (C j)"
              by (intro ballI, rule subspace_topology_trans) blast
            show "closedin_on ?Y2 ?TY2 D \<Longrightarrow>
                \<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D)"
              using hiff htrans by (by100 simp)
            show "(\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D)) \<Longrightarrow>
                closedin_on ?Y2 ?TY2 D"
              using hiff htrans by (by100 simp)
          qed
          from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge2 hF2fin
              hg_F2 hbase_F2 hC_data_F2 hC_union_F2 hC_disj_F2 hC_closed_F2]
          obtain G2 :: "int set" and mul2 e2 invg2 and \<eta>2 :: "'i \<Rightarrow> int" and \<Phi>2
            where hfree2: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2 ?F2"
              and hiso2: "top1_group_iso_on G2 mul2
                  (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                  (top1_fundamental_group_mul ?Y2 ?TY2 p) \<Phi>2"
              and hgens2: "\<forall>j\<in>?F2. \<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                  (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
            by (by100 blast)
          \<comment> \<open>Step 2: \\<pi>\\_1(?Y2) is generated by [gen\\_loop \\<alpha>] for \\<alpha> \\<in> ?F2.\<close>
          \<comment> \<open>Condition 4 of free\\_group\\_full\\_on: G2 = subgroup\\_generated(\\<eta>2 ` ?F2).\<close>
          have hG2_gen: "G2 = top1_subgroup_generated_on G2 mul2 e2 invg2 (\<eta>2 ` ?F2)"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          have hG2_grp: "top1_is_group_on G2 mul2 e2 invg2"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          \<comment> \<open>\\<Phi>2 is a surjective hom G2 \\<rightarrow> \\<pi>\\_1(?Y2).\<close>
          have hPhi2_surj: "\<Phi>2 ` G2 = top1_fundamental_group_carrier ?Y2 ?TY2 p"
            using hiso2 unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
          have hPhi2_hom: "top1_group_hom_on G2 mul2
              (top1_fundamental_group_carrier ?Y2 ?TY2 p) (top1_fundamental_group_mul ?Y2 ?TY2 p) \<Phi>2"
            using hiso2 unfolding top1_group_iso_on_def by (by100 blast)
          have hpi1Y2_grp: "top1_is_group_on
              (top1_fundamental_group_carrier ?Y2 ?TY2 p) (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p) (top1_fundamental_group_invg ?Y2 ?TY2 p)"
            by (rule top1_fundamental_group_is_group[OF hTY2 hpY2])
          \<comment> \<open>By surjective\\_hom\\_preserves\\_generation: \\<pi>\\_1(?Y2) = subgroup\\_generated(\\<Phi>2 ` \\<eta>2 ` ?F2).\<close>
          have h\<eta>2_sub: "\<eta>2 ` ?F2 \<subseteq> G2"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          from surjective_hom_preserves_generation[OF hG2_grp hpi1Y2_grp hG2_gen
              hPhi2_hom hPhi2_surj h\<eta>2_sub]
          have hpi1Y2_gen: "top1_fundamental_group_carrier ?Y2 ?TY2 p =
              top1_subgroup_generated_on (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                  (top1_fundamental_group_mul ?Y2 ?TY2 p)
                  (top1_fundamental_group_id ?Y2 ?TY2 p)
                  (top1_fundamental_group_invg ?Y2 ?TY2 p) (\<Phi>2 ` \<eta>2 ` ?F2)" .
          \<comment> \<open>\\<Phi>2(\\<eta>2(\\<alpha>)) = [gen\\_loop \\<alpha>]\\_{?Y2} (from hgens2 + gen\\_loop\\_def).\<close>
          define S_Y2 where "S_Y2 = (\<lambda>\<alpha>. {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}) ` ?F2"
          have hPhi_eta_eq: "\<Phi>2 ` \<eta>2 ` ?F2 = S_Y2"
            unfolding S_Y2_def
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> \<Phi>2 ` \<eta>2 ` ?F2"
            then obtain \<alpha> where "\<alpha> \<in> ?F2" "x = \<Phi>2 (\<eta>2 \<alpha>)" by (by100 blast)
            from hgens2[rule_format, OF \<open>\<alpha> \<in> ?F2\<close>]
            have "\<Phi>2 (\<eta>2 \<alpha>) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}" .
            hence "x = {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}"
              using \<open>x = \<Phi>2 (\<eta>2 \<alpha>)\<close> unfolding gen_loop_def by (by100 blast)
            thus "x \<in> (\<lambda>\<alpha>. {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}) ` ?F2"
              using \<open>\<alpha> \<in> ?F2\<close> by (by100 blast)
          next
            fix x assume "x \<in> (\<lambda>\<alpha>. {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}) ` ?F2"
            then obtain \<alpha> where "\<alpha> \<in> ?F2"
              "x = {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}" by (by100 blast)
            from hgens2[rule_format, OF \<open>\<alpha> \<in> ?F2\<close>]
            have "\<Phi>2 (\<eta>2 \<alpha>) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                (\<lambda>t. g \<alpha> (cos (2 * pi * t), sin (2 * pi * t))) l}" .
            hence "x = \<Phi>2 (\<eta>2 \<alpha>)"
              using \<open>x = _\<close> unfolding gen_loop_def by (by100 blast)
            thus "x \<in> \<Phi>2 ` \<eta>2 ` ?F2" using \<open>\<alpha> \<in> ?F2\<close> by (by100 blast)
          qed
          \<comment> \<open>Step 3: The inclusion hom \\<pi>\\_1(?Y2) \\<rightarrow> \\<pi>\\_1(X).\<close>
          let ?incl = "top1_fundamental_group_induced_on ?Y2 ?TY2 p X TX p (\<lambda>x. x)"
          have hincl_hom: "top1_group_hom_on
              (top1_fundamental_group_carrier ?Y2 ?TY2 p)
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p) ?incl"
            by (rule subspace_inclusion_induced_hom[OF hTX hY2_sub hpY2])
          \<comment> \<open>Step 4: inclusion maps [gen\\_loop \\<alpha>]\\_{?Y2} to \\<iota>(\\<alpha>) = [gen\\_loop \\<alpha>]\\_X.\<close>
          have hincl_gen: "\<forall>\<alpha>\<in>?F2.
              ?incl {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l} = \<iota> \<alpha>"
          proof (intro ballI)
            fix \<alpha> assume h\<alpha>F: "\<alpha> \<in> ?F2"
            show "?incl {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l} = \<iota> \<alpha>"
              unfolding top1_fundamental_group_induced_on_def \<iota>_def
            proof (rule set_eqI, rule iffI)
              fix h assume "h \<in> {g. \<exists>f\<in>{l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}.
                  top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f) g}"
              then obtain f' where hf'_eq: "top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) f'"
                  and hh_eq: "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
              \<comment> \<open>loop\\_equiv in ?Y2 implies loop\\_equiv in X.\<close>
              have h\<alpha>J': "\<alpha> \<in> J" using h\<alpha>F hF2J by (by100 blast)
              have hgen_\<alpha>_loop_X: "top1_is_loop_on X TX p (gen_loop \<alpha>)"
                using hgen h\<alpha>J' by (by100 blast)
              have "top1_loop_equiv_on X TX p (gen_loop \<alpha>) f'"
              proof -
                from hf'_eq[unfolded top1_loop_equiv_on_def]
                have hf'_path: "top1_path_homotopic_on ?Y2 ?TY2 p p (gen_loop \<alpha>) f'" by (by100 blast)
                have hf'_loop_Y2: "top1_is_loop_on ?Y2 ?TY2 p f'"
                  using hf'_eq unfolding top1_loop_equiv_on_def by (by100 blast)
                have hf'_loop_X: "top1_is_loop_on X TX p f'"
                proof -
                  have hf'_cont_Y2: "top1_continuous_map_on I_set I_top ?Y2 ?TY2 f'"
                    using hf'_loop_Y2 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  have "top1_continuous_map_on I_set I_top X TX (id \<circ> f')"
                    by (rule top1_continuous_map_on_comp[OF hf'_cont_Y2
                      Theorem_18_2(2)[OF hTX hTX hTX, rule_format, OF hY2_sub]])
                  hence "top1_continuous_map_on I_set I_top X TX f'" by (by100 simp)
                  moreover have "f' 0 = p" "f' 1 = p"
                    using hf'_loop_Y2 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                  ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                qed
                from path_homotopic_subspace_to_ambient[OF hTX hY2_sub _ hf'_path]
                have "top1_path_homotopic_on X TX p p (gen_loop \<alpha>) f'" by (by100 blast)
                thus ?thesis unfolding top1_loop_equiv_on_def
                  using hgen_\<alpha>_loop_X hf'_loop_X by (by100 blast)
              qed
              have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
              have "top1_loop_equiv_on X TX p f' h" using hh_eq \<open>(\<lambda>x. x) \<circ> f' = f'\<close> by (by100 simp)
              from top1_loop_equiv_on_trans[OF hTX
                \<open>top1_loop_equiv_on X TX p (gen_loop \<alpha>) f'\<close> this]
              show "h \<in> {g. top1_loop_equiv_on X TX p (gen_loop \<alpha>) g}" by (by100 blast)
            next
              fix h assume "h \<in> {g. top1_loop_equiv_on X TX p (gen_loop \<alpha>) g}"
              hence hh: "top1_loop_equiv_on X TX p (gen_loop \<alpha>) h" by (by100 blast)
              have h\<alpha>J: "\<alpha> \<in> J" using h\<alpha>F hF2J by (by100 blast)
              have "top1_is_loop_on ?Y2 ?TY2 p (gen_loop \<alpha>)"
              proof -
                have hgl_loop_X: "top1_is_loop_on X TX p (gen_loop \<alpha>)"
                  using hgen h\<alpha>F hF2J by (by100 blast)
                have hgl_cont_X: "top1_continuous_map_on I_set I_top X TX (gen_loop \<alpha>)"
                  using hgl_loop_X unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                have hgl_im: "(gen_loop \<alpha>) ` I_set \<subseteq> ?Y2"
                  using hgen h\<alpha>F hF2J by (by100 blast)
                have hI_top: "is_topology_on I_set I_top"
                  using top1_unit_interval_topology_is_topology_on .
                from Theorem_18_2(5)[OF hI_top hTX hTX, rule_format]
                  hgl_cont_X hgl_im hY2_sub
                have "top1_continuous_map_on I_set I_top ?Y2 ?TY2 (gen_loop \<alpha>)" by (by100 blast)
                moreover have "(gen_loop \<alpha>) 0 = p" "(gen_loop \<alpha>) 1 = p"
                  using hgl_loop_X unfolding top1_is_loop_on_def top1_is_path_on_def
                  by (by100 blast)+
                ultimately show ?thesis
                  unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
              qed
              from top1_loop_equiv_on_refl[OF this]
              have "top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) (gen_loop \<alpha>)" .
              moreover have "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> gen_loop \<alpha>) h"
              proof -
                have "(\<lambda>x. x) \<circ> gen_loop \<alpha> = gen_loop \<alpha>" by (by100 auto)
                thus ?thesis using hh by (by100 simp)
              qed
              ultimately show "h \<in> {g. \<exists>f\<in>{l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}.
                  top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f) g}" by (by100 blast)
            qed
          qed
          \<comment> \<open>Step 5: ?incl maps S\\_Y2 into subgroup\\_generated(\\<iota>`J).\<close>
          have hincl_S_in_gen: "?incl ` S_Y2 \<subseteq>
              top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
                  (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
                  (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
          proof
            fix y assume "y \<in> ?incl ` S_Y2"
            then obtain \<alpha> where h\<alpha>F: "\<alpha> \<in> ?F2" and
              hy_eq: "y = ?incl {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}"
              unfolding S_Y2_def by (by100 blast)
            have "y = \<iota> \<alpha>" using hy_eq hincl_gen h\<alpha>F by (by100 blast)
            have "\<alpha> \<in> J" using h\<alpha>F hF2J by (by100 blast)
            hence "\<iota> \<alpha> \<in> \<iota> ` J" by (by100 blast)
            have "top1_is_loop_on X TX p (gen_loop \<alpha>)" using hgen \<open>\<alpha> \<in> J\<close> by (by100 blast)
            hence "\<iota> \<alpha> \<in> top1_fundamental_group_carrier X TX p"
              unfolding \<iota>_def top1_fundamental_group_carrier_def by (by100 blast)
            have "\<iota> ` J \<subseteq> top1_fundamental_group_carrier X TX p"
            proof
              fix x assume "x \<in> \<iota> ` J"
              then obtain s where "s \<in> J" "x = \<iota> s" by (by100 blast)
              thus "x \<in> top1_fundamental_group_carrier X TX p"
                using hgen unfolding \<iota>_def top1_fundamental_group_carrier_def by (by100 blast)
            qed
            from subgroup_generated_contains[OF
              top1_fundamental_group_is_group[OF hTX hp] this \<open>\<iota> \<alpha> \<in> \<iota> ` J\<close>]
            show "y \<in> top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
                (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
                (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
              using \<open>y = \<iota> \<alpha>\<close> by (by100 simp)
          qed
          \<comment> \<open>Step 6: The subgroup\\_generated(\\<iota>`J) is a subgroup, so we can apply
             hom\\_image\\_in\\_subgroup\\_from\\_generators.\<close>
          let ?N = "top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
              (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
          have h\<iota>J_sub: "\<iota> ` J \<subseteq> top1_fundamental_group_carrier X TX p"
          proof
            fix x assume "x \<in> \<iota> ` J"
            then obtain s where "s \<in> J" "x = \<iota> s" by (by100 blast)
            thus "x \<in> top1_fundamental_group_carrier X TX p"
              using hgen unfolding \<iota>_def top1_fundamental_group_carrier_def by (by100 blast)
          qed
          have hN_grp: "top1_is_group_on ?N
              (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
              (top1_fundamental_group_invg X TX p)"
            by (rule intersection_of_subgroups_is_group[OF
              top1_fundamental_group_is_group[OF hTX hp] h\<iota>J_sub])
          have hN_sub: "?N \<subseteq> top1_fundamental_group_carrier X TX p"
            by (rule subgroup_generated_subset[OF top1_fundamental_group_is_group[OF hTX hp] h\<iota>J_sub])
          \<comment> \<open>Step 7: \\<pi>\\_1(?Y2) generated by S\\_Y2. Inclusion maps S\\_Y2 into ?N. Hence image \\<subseteq> ?N.\<close>
          have hpi1Y2_gen': "top1_fundamental_group_carrier ?Y2 ?TY2 p =
              top1_subgroup_generated_on (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                  (top1_fundamental_group_mul ?Y2 ?TY2 p) (top1_fundamental_group_id ?Y2 ?TY2 p)
                  (top1_fundamental_group_invg ?Y2 ?TY2 p) S_Y2"
            using hpi1Y2_gen hPhi_eta_eq by (by100 simp)
          have hS_Y2_sub: "S_Y2 \<subseteq> top1_fundamental_group_carrier ?Y2 ?TY2 p"
          proof
            fix x assume "x \<in> S_Y2"
            then obtain \<alpha> where "\<alpha> \<in> ?F2" "x = {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop \<alpha>) l}"
              unfolding S_Y2_def by (by100 blast)
            have h\<alpha>J'': "\<alpha> \<in> J" using \<open>\<alpha> \<in> ?F2\<close> hF2J by (by100 blast)
            have "top1_is_loop_on ?Y2 ?TY2 p (gen_loop \<alpha>)"
            proof -
              have hgl_cont: "top1_continuous_map_on I_set I_top X TX (gen_loop \<alpha>)"
                using hgen h\<alpha>J'' unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
              have hgl_im: "(gen_loop \<alpha>) ` I_set \<subseteq> ?Y2"
                using hgen h\<alpha>J'' \<open>\<alpha> \<in> ?F2\<close> by (by100 blast)
              from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                  rule_format] hgl_cont hgl_im hY2_sub
              have "top1_continuous_map_on I_set I_top ?Y2 ?TY2 (gen_loop \<alpha>)" by (by100 blast)
              moreover have "(gen_loop \<alpha>) 0 = p" "(gen_loop \<alpha>) 1 = p"
                using hgen h\<alpha>J'' unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
              ultimately show ?thesis
                unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            qed
            thus "x \<in> top1_fundamental_group_carrier ?Y2 ?TY2 p"
              using \<open>x = _\<close> unfolding top1_fundamental_group_carrier_def by (by100 blast)
          qed
          from hom_image_in_subgroup_from_generators[OF hpi1Y2_grp
              top1_fundamental_group_is_group[OF hTX hp]
              hincl_hom hpi1Y2_gen' hS_Y2_sub hN_grp hN_sub]
          have himage_in_N: "?incl ` top1_fundamental_group_carrier ?Y2 ?TY2 p \<subseteq> ?N"
            using hincl_S_in_gen by (by100 blast)
          \<comment> \<open>Step 8: c = [f]\\_X is in the image of the inclusion.\<close>
          have "c \<in> ?incl ` top1_fundamental_group_carrier ?Y2 ?TY2 p"
          proof -
            \<comment> \<open>f is a loop in ?Y2.\<close>
            have hf_cont_X: "top1_continuous_map_on I_set I_top X TX f"
              using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            have hf_im_Y2: "f ` I_set \<subseteq> ?Y2"
            proof
              fix x assume "x \<in> f ` I_set"
              thus "x \<in> ?Y2" using hf_in_F by (by100 blast)
            qed
            from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                rule_format] hf_cont_X hf_im_Y2 hY2_sub
            have hf_cont_Y2: "top1_continuous_map_on I_set I_top ?Y2 ?TY2 f" by (by100 blast)
            have hf_loop_Y2: "top1_is_loop_on ?Y2 ?TY2 p f"
              unfolding top1_is_loop_on_def top1_is_path_on_def
              using hf_cont_Y2 hf unfolding top1_is_loop_on_def top1_is_path_on_def
              by (by100 blast)
            \<comment> \<open>[f]\\_{?Y2} \\<in> \\<pi>\\_1(?Y2).\<close>
            let ?cl = "{h. top1_loop_equiv_on ?Y2 ?TY2 p f h}"
            have "?cl \<in> top1_fundamental_group_carrier ?Y2 ?TY2 p"
              unfolding top1_fundamental_group_carrier_def using hf_loop_Y2 by (by100 blast)
            \<comment> \<open>?incl ?cl = c.\<close>
            moreover have "?incl ?cl = c"
            proof -
              have "?incl ?cl = {h. \<exists>f'\<in>?cl. top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h}"
                unfolding top1_fundamental_group_induced_on_def by (by100 blast)
              also have "... = {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                  top1_loop_equiv_on X TX p f' h}"
              proof (rule set_eqI, rule iffI)
                fix h assume "h \<in> {h. \<exists>f'\<in>?cl. top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h}"
                then obtain f' where hf'cl: "top1_loop_equiv_on ?Y2 ?TY2 p f f'"
                    and hf'h: "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
                have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
                hence "top1_loop_equiv_on X TX p f' h" using hf'h by (by100 simp)
                thus "h \<in> {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                    top1_loop_equiv_on X TX p f' h}" using hf'cl by (by100 blast)
              next
                fix h assume "h \<in> {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                    top1_loop_equiv_on X TX p f' h}"
                then obtain f' where hf'eq: "top1_loop_equiv_on ?Y2 ?TY2 p f f'"
                    and hf'h: "top1_loop_equiv_on X TX p f' h" by (by100 blast)
                have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
                hence "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h" using hf'h by (by100 simp)
                thus "h \<in> {h. \<exists>f'\<in>?cl. top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h}"
                  using hf'eq by (by100 blast)
              qed
              also have "... = c"
              proof (rule set_eqI, rule iffI)
                fix h assume "h \<in> {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                    top1_loop_equiv_on X TX p f' h}"
                then obtain f' where hf'eq: "top1_loop_equiv_on ?Y2 ?TY2 p f f'"
                    and hf'h: "top1_loop_equiv_on X TX p f' h" by (by100 blast)
                have "top1_loop_equiv_on X TX p f f'"
                proof -
                  from hf'eq[unfolded top1_loop_equiv_on_def]
                  have "top1_path_homotopic_on ?Y2 ?TY2 p p f f'" by (by100 blast)
                  from path_homotopic_subspace_to_ambient[OF hTX hY2_sub _ this]
                  have "top1_path_homotopic_on X TX p p f f'" by (by100 blast)
                  have "top1_is_loop_on X TX p f'"
                    using hf'h unfolding top1_loop_equiv_on_def by (by100 blast)
                  thus ?thesis unfolding top1_loop_equiv_on_def using hf \<open>top1_is_loop_on X TX p f'\<close>
                    \<open>top1_path_homotopic_on X TX p p f f'\<close> by (by100 blast)
                qed
                from top1_loop_equiv_on_trans[OF hTX this hf'h]
                show "h \<in> c" unfolding hc_eq by (by100 blast)
              next
                fix h assume "h \<in> c"
                hence "top1_loop_equiv_on X TX p f h" unfolding hc_eq by (by100 blast)
                \<comment> \<open>Take f' = f. loop\\_equiv(?Y2, f, f) by reflexivity.\<close>
                moreover have "top1_loop_equiv_on ?Y2 ?TY2 p f f"
                  by (rule top1_loop_equiv_on_refl[OF hf_loop_Y2])
                ultimately show "h \<in> {h. \<exists>f'. top1_loop_equiv_on ?Y2 ?TY2 p f f' \<and>
                    top1_loop_equiv_on X TX p f' h}" by (by100 blast)
              qed
              finally show ?thesis .
            qed
            ultimately show ?thesis by (by100 blast)
          qed
          thus "c \<in> ?N" using himage_in_N by (by100 blast)
        qed
      next
        fix c assume "c \<in> top1_subgroup_generated_on (top1_fundamental_group_carrier X TX p)
            (top1_fundamental_group_mul X TX p) (top1_fundamental_group_id X TX p)
            (top1_fundamental_group_invg X TX p) (\<iota> ` J)"
        have "\<iota> ` J \<subseteq> top1_fundamental_group_carrier X TX p"
        proof
          fix x assume "x \<in> \<iota> ` J"
          then obtain s where "s \<in> J" "x = \<iota> s" by (by100 blast)
          thus "x \<in> top1_fundamental_group_carrier X TX p"
            using hgen unfolding \<iota>_def top1_fundamental_group_carrier_def
            by (by100 blast)
        qed
        from subgroup_generated_subset[OF top1_fundamental_group_is_group[OF hTX hp] this]
        show "c \<in> top1_fundamental_group_carrier X TX p"
          using \<open>c \<in> top1_subgroup_generated_on _ _ _ _ _\<close> by (by100 blast)
      qed
      show "\<forall>ws::('i \<times> bool) list.
          ws \<noteq> [] \<longrightarrow>
          top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<longrightarrow>
          (\<forall>i<length ws. fst (ws ! i) \<in> J) \<longrightarrow>
          top1_group_word_product (top1_fundamental_group_mul X TX p)
              (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
              (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> top1_fundamental_group_id X TX p"
      proof (intro allI impI)
        fix ws :: "('i \<times> bool) list"
        assume hws_ne: "ws \<noteq> []"
          and hred: "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws)"
          and hws_in: "\<forall>i<length ws. fst (ws ! i) \<in> J"
        \<comment> \<open>The word uses finitely many generators.\<close>
        let ?gens = "fst ` set ws"
        have hgens_fin: "finite ?gens" by (by100 simp)
        have hgens_J: "?gens \<subseteq> J"
        proof
          fix \<alpha> assume "\<alpha> \<in> ?gens"
          then obtain sb where "sb \<in> set ws" "fst sb = \<alpha>" by (by100 blast)
          from \<open>sb \<in> set ws\<close> have "\<exists>i. i < length ws \<and> ws ! i = sb"
            using in_set_conv_nth by (by5000 metis)
          then obtain i where "i < length ws" "ws ! i = sb" by (by100 blast)
          have "fst (ws ! i) \<in> J" using hws_in \<open>i < length ws\<close> by (by100 blast)
          thus "\<alpha> \<in> J" using \<open>fst sb = \<alpha>\<close> \<open>ws ! i = sb\<close> by (by100 simp)
        qed
        \<comment> \<open>Each generator loop lies in its circle. The word product loop lies in \\<Union>?gens C\\_\\<alpha>.\<close>
        \<comment> \<open>By hloop\\_finite, the word product is in a finite sub-wedge F \\<supseteq> ?gens.
           By hfinite\\_free, \\<Union>F C\\_\\<alpha> is a wedge. By Theorem\\_71\\_3\\_finite, \\<pi>\\_1 free on F.
           The word is non-trivial in \\<pi>\\_1(\\<Union>F C\\_\\<alpha>). By hhtpy\\_finite,
           the inclusion is injective. So the word is non-trivial in \\<pi>\\_1(X).\<close>
        \<comment> \<open>Proof by contradiction: assume the word product = id in \\<pi>\\_1(X).
           The word uses generators from ?gens \\<subseteq> J. Take the sub-wedge \\<Union>?gens C\\_\\<alpha>.
           The word is non-trivial there by freeness. But it's trivial in \\<pi>\\_1(X),
           and by hhtpy\\_finite + expanding to a larger sub-wedge, it's trivial in
           some sub-wedge containing ?gens. Contradiction.\<close>
        \<comment> \<open>Proof: the word product in \\<pi>\\_1(X) is the image of the word product in
           \\<pi>\\_1(\\<Union>?gens C\\_\\<alpha>) under the inclusion homomorphism.
           In the sub-wedge, the word is non-trivial by freeness (condition 5).
           The inclusion hom preserves this via hom\\_word\\_product.\<close>
        show "top1_group_word_product (top1_fundamental_group_mul X TX p)
            (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
            (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> top1_fundamental_group_id X TX p"
        proof -
          have "J \<noteq> {}" using hp hcover by (by100 blast)
          then obtain \<gamma> where "\<gamma> \<in> J" by (by100 blast)
          let ?F2 = "?gens \<union> {\<gamma>}"
          have hF2fin: "finite ?F2" using hgens_fin by (by100 simp)
          have hF2J: "?F2 \<subseteq> J" using hgens_J \<open>\<gamma> \<in> J\<close> by (by100 blast)
          have hF2ne: "?F2 \<noteq> {}" by (by100 blast)
          have hgens_sub_F2: "?gens \<subseteq> ?F2" by (by100 blast)
          let ?Y2 = "\<Union>\<alpha>\<in>?F2. C \<alpha>"
          let ?TY2 = "subspace_topology X TX ?Y2"
          have hY2_sub: "?Y2 \<subseteq> X" using hC hF2J by (by100 blast)
          have hpY2: "p \<in> ?Y2" using hC \<open>\<gamma> \<in> J\<close> by (by100 blast)
          have hTY2: "is_topology_on ?Y2 ?TY2"
            by (rule subspace_topology_is_topology_on[OF hTX hY2_sub])
          from hfinite_free[OF hF2fin hF2J hF2ne]
          have hwedge2: "top1_is_wedge_of_circles_on ?Y2 ?TY2 ?F2 p" .
          \<comment> \<open>Apply finite\\_wedge\\_pi1\\_free\\_with\\_chosen\\_loops\\_arb.\<close>
          have hg_F2: "\<forall>j\<in>?F2. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology ?Y2 ?TY2 (C j)) (g j)"
          proof -
            {
              fix j assume hjF: "j \<in> ?F2"
              hence "j \<in> J" using hF2J by (by100 blast)
              have hgj: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology X TX (C j)) (g j)" using hg \<open>j \<in> J\<close> by (by100 blast)
              have "subspace_topology ?Y2 ?TY2 (C j) = subspace_topology X TX (C j)"
                by (rule subspace_topology_trans) (use hjF in blast)
              hence "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology ?Y2 ?TY2 (C j)) (g j)"
                using hgj by (by100 simp)
            }
            thus ?thesis by (by100 blast)
          qed
          have hC_closed_F2: "\<forall>D\<subseteq>?Y2. closedin_on ?Y2 ?TY2 D \<longleftrightarrow>
              (\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D))"
          proof (intro allI impI iffI)
            fix D assume hD: "D \<subseteq> ?Y2"
            from hcoh_sub[OF hF2J, rule_format, OF hD]
            have hiff: "closedin_on ?Y2 ?TY2 D \<longleftrightarrow>
                (\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))" .
            have htrans: "\<forall>j\<in>?F2. subspace_topology ?Y2 ?TY2 (C j) = subspace_topology X TX (C j)"
              by (intro ballI, rule subspace_topology_trans) blast
            show "closedin_on ?Y2 ?TY2 D \<Longrightarrow>
                \<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D)"
              using hiff htrans by (by100 simp)
            show "(\<forall>j\<in>?F2. closedin_on (C j) (subspace_topology ?Y2 ?TY2 (C j)) (C j \<inter> D)) \<Longrightarrow>
                closedin_on ?Y2 ?TY2 D"
              using hiff htrans by (by100 simp)
          qed
          have hbase_F2: "\<forall>j\<in>?F2. g j (1, 0) = p" using hg hF2J by (by100 blast)
          have hC_data_F2: "\<forall>j\<in>?F2. C j \<subseteq> ?Y2 \<and> p \<in> C j" using hC hF2J by (by100 blast)
          have hC_union_F2: "(\<Union>j\<in>?F2. C j) = ?Y2" by (by100 blast)
          have hC_disj_F2: "\<forall>i\<in>?F2. \<forall>j\<in>?F2. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
            using hdisjoint hF2J by (by100 blast)
          from finite_wedge_pi1_free_with_chosen_loops_arb[OF hwedge2 hF2fin
              hg_F2 hbase_F2 hC_data_F2 hC_union_F2 hC_disj_F2 hC_closed_F2]
          obtain G2 :: "int set" and mul2 e2 invg2 and \<eta>2 :: "'i \<Rightarrow> int" and \<Phi>2
            where hfree2: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2 ?F2"
              and hiso2: "top1_group_iso_on G2 mul2
                  (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                  (top1_fundamental_group_mul ?Y2 ?TY2 p) \<Phi>2"
              and hgens2: "\<forall>j\<in>?F2. \<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                  (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l}"
            by (by100 blast)
          \<comment> \<open>Condition 5 of free group: reduced non-empty word \\<noteq> e.\<close>
          have hfree_cond5: "\<And>ws'. ws' \<noteq> [] \<Longrightarrow>
              top1_is_reduced_word (map (\<lambda>(s, b). (\<eta>2 s, b)) ws') \<Longrightarrow>
              (\<forall>i<length ws'. fst (ws' ! i) \<in> ?F2) \<Longrightarrow>
              top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s, b). (\<eta>2 s, b)) ws') \<noteq> e2"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          \<comment> \<open>Our word ws has generators from ?gens \\<subseteq> ?F2.
             The word in \\<eta>2-form is reduced (since \\<eta>2 is injective and the original word is reduced).
             By condition 5, word\\_product(G2, ...) \\<noteq> e2.\<close>
          \<comment> \<open>Via iso \\<Phi>2: word\\_product(\\<pi>\\_1(?Y2), ...) \\<noteq> id\\_{?Y2}.\<close>
          \<comment> \<open>Via inclusion hom: word\\_product(\\<pi>\\_1(X), ...) = word\\_product in X.\<close>
          \<comment> \<open>The inclusion sends [gen\\_loop \\<alpha>]\\_{?Y2} to \\<iota>(\\<alpha>).
             So inclusion(word\\_product(\\<pi>\\_1(?Y2), [(gen\\_loop ws\\_i, b\\_i)])) =
             word\\_product(\\<pi>\\_1(X), [(\\<iota>(ws\\_i), b\\_i)]).\<close>
          \<comment> \<open>If X's word product = id, then sub-wedge's word product maps to id under inclusion.
             Need: inclusion injective \\<Longrightarrow> sub-wedge's word product = id. Contradiction.\<close>
          \<comment> \<open>Inclusion injectivity on this specific element:
             the word product loop has image in \\<Union>?gens \\<subseteq> \\<Union>?F2.
             If null-homotopic in X, the homotopy lies in some \\<Union>F' (hhtpy\\_finite).
             Take F'' = ?F2 \\<union> F'. In \\<Union>F'', the word product is null-homotopic.
             But \\<Union>F'' has free \\<pi>\\_1 and the word is still non-trivial there. Contradiction.\<close>
          \<comment> \<open>Step A: In the free group G2 on ?F2, the word is non-trivial.\<close>
          have hws_in_F2: "\<forall>i<length ws. fst (ws ! i) \<in> ?F2"
          proof (intro allI impI)
            fix i assume "i < length ws"
            have "fst (ws ! i) \<in> J" using hws_in \<open>i < length ws\<close> by (by100 blast)
            have "fst (ws ! i) \<in> ?gens" using \<open>i < length ws\<close> by (by100 force)
            thus "fst (ws ! i) \<in> ?F2" using hgens_sub_F2 by (by100 blast)
          qed
          \<comment> \<open>Step B: The inclusion hom is injective (from hincl\\_inj).\<close>
          let ?incl = "top1_fundamental_group_induced_on ?Y2 ?TY2 p X TX p (\<lambda>x. x)"
          from hincl_inj[OF hF2fin hF2J hF2ne]
          have hincl_injective: "inj_on ?incl
              (top1_fundamental_group_carrier ?Y2 ?TY2 p)" .
          \<comment> \<open>Step C: By the free group structure and inclusion injectivity,
             the word product in \\<pi>\\_1(X) is non-trivial.
             The argument: word non-trivial in \\<pi>\\_1(?Y2) (from condition 5 + iso),
             inclusion injective \\<Longrightarrow> image non-trivial in \\<pi>\\_1(X),
             and hom\\_word\\_product connects word products across the inclusion.\<close>
          \<comment> \<open>Chain: word \\<noteq> e in G2 \\<Rightarrow> word \\<noteq> id in \\<pi>\\_1(?Y2) \\<Rightarrow> word \\<noteq> id in \\<pi>\\_1(X).\<close>
          have h\<eta>2_inj: "inj_on \<eta>2 ?F2"
            using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
          \<comment> \<open>Step C1: word reduced in \\<eta>2-form.\<close>
          have hred_\<eta>2: "top1_is_reduced_word (map (\<lambda>(s, b). (\<eta>2 s, b)) ws)"
          proof (rule reduced_word_transfer[where S="?F2" and h="\<iota>" and g="\<eta>2"])
            show "\<And>s t. s \<in> ?F2 \<Longrightarrow> t \<in> ?F2 \<Longrightarrow> \<eta>2 s = \<eta>2 t \<Longrightarrow> \<iota> s = \<iota> t"
            proof -
              fix s t assume "s \<in> ?F2" "t \<in> ?F2" "\<eta>2 s = \<eta>2 t"
              from \<open>\<eta>2 s = \<eta>2 t\<close> have "s = t"
                using h\<eta>2_inj \<open>s \<in> ?F2\<close> \<open>t \<in> ?F2\<close> unfolding inj_on_def by (by100 blast)
              thus "\<iota> s = \<iota> t" by (by100 simp)
            qed
            show "\<forall>i<length ws. fst (ws ! i) \<in> ?F2" by (rule hws_in_F2)
            show "top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws)" by (rule hred)
          qed
          \<comment> \<open>Step C2: word \\<noteq> e in G2.\<close>
          have hword_ne_G2: "top1_group_word_product mul2 e2 invg2
              (map (\<lambda>(s, b). (\<eta>2 s, b)) ws) \<noteq> e2"
            by (rule hfree_cond5[OF hws_ne hred_\<eta>2 hws_in_F2])
          \<comment> \<open>Step C3: word \\<noteq> id in \\<pi>\\_1(?Y2). Uses iso \\<Phi>2 + hom\\_word\\_product.\<close>
          have hword_ne_Y2: "top1_group_word_product
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p)
              (top1_fundamental_group_invg ?Y2 ?TY2 p)
              (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) \<noteq>
              top1_fundamental_group_id ?Y2 ?TY2 p"
          proof -
            have hG2_grp: "top1_is_group_on G2 mul2 e2 invg2"
              using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
            have hpi1Y2_grp': "top1_is_group_on
                (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                (top1_fundamental_group_mul ?Y2 ?TY2 p)
                (top1_fundamental_group_id ?Y2 ?TY2 p)
                (top1_fundamental_group_invg ?Y2 ?TY2 p)"
              by (rule top1_fundamental_group_is_group[OF hTY2 hpY2])
            have hPhi2_hom: "top1_group_hom_on G2 mul2
                (top1_fundamental_group_carrier ?Y2 ?TY2 p)
                (top1_fundamental_group_mul ?Y2 ?TY2 p) \<Phi>2"
              using hiso2 unfolding top1_group_iso_on_def by (by100 blast)
            have hPhi2_inj: "inj_on \<Phi>2 G2"
              using hiso2 unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
            have h\<eta>2_in_G2: "\<forall>i<length ws. fst (map (\<lambda>(s,b). (\<eta>2 s, b)) ws ! i) \<in> G2"
            proof (intro allI impI)
              fix i assume "i < length ws"
              have "fst (ws ! i) \<in> ?F2" using hws_in_F2 \<open>i < length ws\<close> by (by100 blast)
              hence "\<eta>2 (fst (ws ! i)) \<in> G2"
                using hfree2 unfolding top1_is_free_group_full_on_def by (by100 blast)
              moreover obtain s b where "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
              ultimately show "fst (map (\<lambda>(s,b). (\<eta>2 s, b)) ws ! i) \<in> G2"
                using \<open>i < length ws\<close> by (by100 simp)
            qed
            \<comment> \<open>\\<Phi>2 preserves word products.\<close>
            have h\<eta>2_ws_in_G2: "\<forall>i<length (map (\<lambda>(s,b). (\<eta>2 s, b)) ws).
                fst ((map (\<lambda>(s,b). (\<eta>2 s, b)) ws) ! i) \<in> G2"
              using h\<eta>2_in_G2 by (by100 auto)
            have hPhi2_wp: "\<Phi>2 (top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws)) =
                top1_group_word_product (top1_fundamental_group_mul ?Y2 ?TY2 p)
                    (top1_fundamental_group_id ?Y2 ?TY2 p)
                    (top1_fundamental_group_invg ?Y2 ?TY2 p)
                    (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)"
            proof -
              from hom_word_product[OF hG2_grp hpi1Y2_grp' hPhi2_hom h\<eta>2_ws_in_G2]
              have "\<Phi>2 (top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws)) =
                  top1_group_word_product (top1_fundamental_group_mul ?Y2 ?TY2 p)
                      (top1_fundamental_group_id ?Y2 ?TY2 p)
                      (top1_fundamental_group_invg ?Y2 ?TY2 p)
                      (map (\<lambda>(x, b). (\<Phi>2 x, b)) (map (\<lambda>(s,b). (\<eta>2 s, b)) ws))" .
              moreover have "map (\<lambda>(x, b). (\<Phi>2 x, b)) (map (\<lambda>(s,b). (\<eta>2 s, b)) ws) =
                  map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws" by (by100 auto)
              ultimately show ?thesis by (by5000 metis)
            qed
            \<comment> \<open>Since word(G2) \\<noteq> e2 and \\<Phi>2 injective:\<close>
            have "top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws) \<in> G2"
              by (rule word_product_in_group[OF hG2_grp h\<eta>2_ws_in_G2])
            have "e2 \<in> G2" using hG2_grp unfolding top1_is_group_on_def by (by100 blast)
            have "\<Phi>2 e2 = top1_fundamental_group_id ?Y2 ?TY2 p"
              by (rule hom_preserves_id[OF hG2_grp hpi1Y2_grp' hPhi2_hom])
            show ?thesis
            proof
              assume "top1_group_word_product (top1_fundamental_group_mul ?Y2 ?TY2 p)
                  (top1_fundamental_group_id ?Y2 ?TY2 p)
                  (top1_fundamental_group_invg ?Y2 ?TY2 p)
                  (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) =
                  top1_fundamental_group_id ?Y2 ?TY2 p"
              hence "\<Phi>2 (top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws)) =
                  \<Phi>2 e2"
                using \<open>\<Phi>2 (top1_group_word_product mul2 e2 invg2 _) = _\<close>
                  \<open>\<Phi>2 e2 = _\<close> by (by100 simp)
              hence "top1_group_word_product mul2 e2 invg2 (map (\<lambda>(s,b). (\<eta>2 s, b)) ws) = e2"
                using hPhi2_inj
                  \<open>top1_group_word_product mul2 e2 invg2 _ \<in> G2\<close> \<open>e2 \<in> G2\<close>
                unfolding inj_on_def by (by5000 metis)
              thus False using hword_ne_G2 by contradiction
            qed
          qed
          \<comment> \<open>Step C4: word in \\<pi>\\_1(X) = inclusion of word in \\<pi>\\_1(?Y2).\<close>
          have hincl_hom: "top1_group_hom_on
              (top1_fundamental_group_carrier ?Y2 ?TY2 p)
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_carrier X TX p)
              (top1_fundamental_group_mul X TX p) ?incl"
            by (rule subspace_inclusion_induced_hom[OF hTX hY2_sub hpY2])
          have hincl_maps_word: "?incl (top1_group_word_product
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p)
              (top1_fundamental_group_invg ?Y2 ?TY2 p)
              (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) =
              top1_group_word_product (top1_fundamental_group_mul X TX p)
                  (top1_fundamental_group_id X TX p)
                  (top1_fundamental_group_invg X TX p)
                  (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
          proof -
            have hPhi_eta_in': "\<forall>i<length (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws).
                fst ((map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) ! i) \<in>
                top1_fundamental_group_carrier ?Y2 ?TY2 p"
            proof (intro allI impI)
              fix i assume "i < length (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)"
              hence "i < length ws" by (by100 simp)
              have "fst (ws ! i) \<in> ?F2" using hws_in_F2 \<open>i < length ws\<close> by (by100 blast)
              have "\<eta>2 (fst (ws ! i)) \<in> G2"
                using hfree2 \<open>fst (ws ! i) \<in> ?F2\<close>
                unfolding top1_is_free_group_full_on_def by (by100 blast)
              have "\<Phi>2 (\<eta>2 (fst (ws ! i))) \<in> top1_fundamental_group_carrier ?Y2 ?TY2 p"
                using hiso2 \<open>\<eta>2 (fst (ws ! i)) \<in> G2\<close>
                unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
              moreover obtain s b where "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
              ultimately show "fst ((map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) ! i) \<in>
                  top1_fundamental_group_carrier ?Y2 ?TY2 p"
                using \<open>i < length ws\<close> by (by100 simp)
            qed
            from hom_word_product[OF
                top1_fundamental_group_is_group[OF hTY2 hpY2]
                top1_fundamental_group_is_group[OF hTX hp]
                hincl_hom hPhi_eta_in']
            have "?incl (top1_group_word_product
                (top1_fundamental_group_mul ?Y2 ?TY2 p)
                (top1_fundamental_group_id ?Y2 ?TY2 p)
                (top1_fundamental_group_invg ?Y2 ?TY2 p)
                (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) =
                top1_group_word_product (top1_fundamental_group_mul X TX p)
                    (top1_fundamental_group_id X TX p)
                    (top1_fundamental_group_invg X TX p)
                    (map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws))" .
            moreover have "map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) =
                map (\<lambda>(s,b). (\<iota> s, b)) ws"
            proof -
              have hincl_gen': "\<forall>s\<in>?F2. ?incl (\<Phi>2 (\<eta>2 s)) = \<iota> s"
              proof (intro ballI)
                fix s assume "s \<in> ?F2"
                \<comment> \<open>\\<Phi>2(\\<eta>2 s) = [gen\\_loop s]\\_{Y2}.\<close>
                from hgens2[rule_format, OF \<open>s \<in> ?F2\<close>]
                have "(\<Phi>2 (\<eta>2 s)) = {l. top1_loop_equiv_on ?Y2 ?TY2 p
                    (\<lambda>t. g s (cos (2 * pi * t), sin (2 * pi * t))) l}" .
                hence hPhi_eta_s: "\<Phi>2 (\<eta>2 s) = {l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) l}"
                  unfolding gen_loop_def by (by100 blast)
                \<comment> \<open>?incl [gen\\_loop s]\\_{Y2} = \\<iota>(s).\<close>
                show "?incl (\<Phi>2 (\<eta>2 s)) = \<iota> s"
                  unfolding hPhi_eta_s top1_fundamental_group_induced_on_def \<iota>_def
                proof (rule set_eqI, rule iffI)
                  fix h assume "h \<in> {g. \<exists>f\<in>{l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) l}.
                      top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f) g}"
                  then obtain f' where "top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) f'"
                      "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h" by (by100 blast)
                  have "(\<lambda>x. x) \<circ> f' = f'" by (by100 auto)
                  have "top1_loop_equiv_on X TX p f' h" using \<open>top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f') h\<close>
                    \<open>(\<lambda>x. x) \<circ> f' = f'\<close> by (by100 simp)
                  have "top1_loop_equiv_on X TX p (gen_loop s) f'"
                  proof -
                    from \<open>top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) f'\<close>[unfolded top1_loop_equiv_on_def]
                    have "top1_path_homotopic_on ?Y2 ?TY2 p p (gen_loop s) f'" by (by100 blast)
                    from path_homotopic_subspace_to_ambient[OF hTX hY2_sub _ this]
                    have "top1_path_homotopic_on X TX p p (gen_loop s) f'" by (by100 blast)
                    have "top1_is_loop_on X TX p f'"
                      using \<open>top1_loop_equiv_on X TX p f' h\<close> unfolding top1_loop_equiv_on_def by (by100 blast)
                    have "s \<in> J" using \<open>s \<in> ?F2\<close> hF2J by (by100 blast)
                    have "top1_is_loop_on X TX p (gen_loop s)" using hgen \<open>s \<in> J\<close> by (by100 blast)
                    thus ?thesis unfolding top1_loop_equiv_on_def
                      using \<open>top1_is_loop_on X TX p (gen_loop s)\<close> \<open>top1_is_loop_on X TX p f'\<close>
                        \<open>top1_path_homotopic_on X TX p p (gen_loop s) f'\<close> by (by100 blast)
                  qed
                  from top1_loop_equiv_on_trans[OF hTX this \<open>top1_loop_equiv_on X TX p f' h\<close>]
                  show "h \<in> {g. top1_loop_equiv_on X TX p (gen_loop s) g}" by (by100 blast)
                next
                  fix h assume "h \<in> {g. top1_loop_equiv_on X TX p (gen_loop s) g}"
                  hence "top1_loop_equiv_on X TX p (gen_loop s) h" by (by100 blast)
                  have "s \<in> J" using \<open>s \<in> ?F2\<close> hF2J by (by100 blast)
                  have hgl_loop_Y2: "top1_is_loop_on ?Y2 ?TY2 p (gen_loop s)"
                  proof -
                    have hgl_cont: "top1_continuous_map_on I_set I_top X TX (gen_loop s)"
                      using hgen \<open>s \<in> J\<close> unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                    have hgl_im: "(gen_loop s) ` I_set \<subseteq> ?Y2"
                      using hgen \<open>s \<in> J\<close> \<open>s \<in> ?F2\<close> by (by100 blast)
                    from Theorem_18_2(5)[OF top1_unit_interval_topology_is_topology_on hTX hTX,
                        rule_format] hgl_cont hgl_im hY2_sub
                    have "top1_continuous_map_on I_set I_top ?Y2 ?TY2 (gen_loop s)" by (by100 blast)
                    moreover have "(gen_loop s) 0 = p" "(gen_loop s) 1 = p"
                      using hgen \<open>s \<in> J\<close> unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
                    ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  qed
                  from top1_loop_equiv_on_refl[OF hgl_loop_Y2]
                  have "top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) (gen_loop s)" .
                  moreover have "(\<lambda>x. x) \<circ> gen_loop s = gen_loop s" by (by100 auto)
                  hence "top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> gen_loop s) h"
                    using \<open>top1_loop_equiv_on X TX p (gen_loop s) h\<close> by (by100 simp)
                  ultimately show "h \<in> {g. \<exists>f\<in>{l. top1_loop_equiv_on ?Y2 ?TY2 p (gen_loop s) l}.
                      top1_loop_equiv_on X TX p ((\<lambda>x. x) \<circ> f) g}" by (by100 blast)
                qed
              qed
              have hincl_ptwise: "\<forall>i<length ws. ?incl (\<Phi>2 (\<eta>2 (fst (ws ! i)))) = \<iota> (fst (ws ! i))"
              proof (intro allI impI)
                fix i assume "i < length ws"
                have "fst (ws ! i) \<in> ?F2" using hws_in_F2 \<open>i < length ws\<close> by (by100 blast)
                thus "?incl (\<Phi>2 (\<eta>2 (fst (ws ! i)))) = \<iota> (fst (ws ! i))"
                  using hincl_gen' by (by100 blast)
              qed
              show ?thesis
              proof (rule nth_equalityI)
                show "length (map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) =
                    length (map (\<lambda>(s,b). (\<iota> s, b)) ws)" by (by100 simp)
              next
                fix i assume "i < length (map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws))"
                hence hi: "i < length ws" by (by100 simp)
                obtain s b where hsb: "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
                have "?incl (\<Phi>2 (\<eta>2 s)) = \<iota> s"
                  using hincl_ptwise hi hsb by (by100 force)
                thus "(map (\<lambda>(x, b). (?incl x, b)) (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) ! i =
                    (map (\<lambda>(s,b). (\<iota> s, b)) ws) ! i"
                  using hi hsb by (by100 simp)
              qed
            qed
            ultimately show ?thesis by (by5000 metis)
          qed
          \<comment> \<open>Step C5: word \\<noteq> id in \\<pi>\\_1(X). Uses inclusion injectivity.\<close>
          have hPhi_eta_in_carrier: "\<forall>i<length ws.
              fst (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws ! i) \<in>
              top1_fundamental_group_carrier ?Y2 ?TY2 p"
          proof (intro allI impI)
            fix i assume "i < length ws"
            have "fst (ws ! i) \<in> ?F2" using hws_in_F2 \<open>i < length ws\<close> by (by100 blast)
            have "\<eta>2 (fst (ws ! i)) \<in> G2"
              using hfree2 \<open>fst (ws ! i) \<in> ?F2\<close>
              unfolding top1_is_free_group_full_on_def by (by100 blast)
            have "\<Phi>2 (\<eta>2 (fst (ws ! i))) \<in> top1_fundamental_group_carrier ?Y2 ?TY2 p"
              using hiso2 \<open>\<eta>2 (fst (ws ! i)) \<in> G2\<close>
              unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
            moreover obtain s b where "ws ! i = (s, b)" by (cases "ws ! i") (by100 blast)
            ultimately show "fst (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws ! i) \<in>
                top1_fundamental_group_carrier ?Y2 ?TY2 p"
              using \<open>i < length ws\<close> by (by100 simp)
          qed
          have hpi1Y2_grp: "top1_is_group_on
              (top1_fundamental_group_carrier ?Y2 ?TY2 p)
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p)
              (top1_fundamental_group_invg ?Y2 ?TY2 p)"
            by (rule top1_fundamental_group_is_group[OF hTY2 hpY2])
          have hword_in_carrier: "top1_group_word_product
              (top1_fundamental_group_mul ?Y2 ?TY2 p)
              (top1_fundamental_group_id ?Y2 ?TY2 p)
              (top1_fundamental_group_invg ?Y2 ?TY2 p)
              (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) \<in>
              top1_fundamental_group_carrier ?Y2 ?TY2 p"
          proof -
            have "\<forall>i<length (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws).
                fst ((map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) ! i) \<in>
                top1_fundamental_group_carrier ?Y2 ?TY2 p"
              using hPhi_eta_in_carrier by (by100 auto)
            from word_product_in_group[OF hpi1Y2_grp this] show ?thesis .
          qed
          have hid_in_carrier: "top1_fundamental_group_id ?Y2 ?TY2 p \<in>
              top1_fundamental_group_carrier ?Y2 ?TY2 p"
            using hpi1Y2_grp unfolding top1_is_group_on_def by (by100 blast)
          have hincl_id: "?incl (top1_fundamental_group_id ?Y2 ?TY2 p) =
              top1_fundamental_group_id X TX p"
            by (rule hom_preserves_id[OF hpi1Y2_grp
              top1_fundamental_group_is_group[OF hTX hp] hincl_hom])
          show ?thesis
          proof
            assume heq: "top1_group_word_product (top1_fundamental_group_mul X TX p)
                (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
                (map (\<lambda>(s, b). (\<iota> s, b)) ws) = top1_fundamental_group_id X TX p"
            \<comment> \<open>?incl(word(Y2)) = word(X) = id\\_X = ?incl(id\\_Y2).\<close>
            have "?incl (top1_group_word_product
                (top1_fundamental_group_mul ?Y2 ?TY2 p)
                (top1_fundamental_group_id ?Y2 ?TY2 p)
                (top1_fundamental_group_invg ?Y2 ?TY2 p)
                (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws)) =
                ?incl (top1_fundamental_group_id ?Y2 ?TY2 p)"
              using hincl_maps_word heq hincl_id by (by100 simp)
            \<comment> \<open>By injectivity: word(Y2) = id\\_Y2.\<close>
            hence "top1_group_word_product
                (top1_fundamental_group_mul ?Y2 ?TY2 p)
                (top1_fundamental_group_id ?Y2 ?TY2 p)
                (top1_fundamental_group_invg ?Y2 ?TY2 p)
                (map (\<lambda>(s,b). (\<Phi>2 (\<eta>2 s), b)) ws) =
                top1_fundamental_group_id ?Y2 ?TY2 p"
              using hincl_injective hword_in_carrier hid_in_carrier
              unfolding inj_on_def by (by5000 metis)
            \<comment> \<open>But word(Y2) \\<noteq> id\\_Y2. Contradiction.\<close>
            thus False using hword_ne_Y2 by contradiction
          qed
        qed
      qed
    qed
  qed
qed

end
