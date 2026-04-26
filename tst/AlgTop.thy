theory AlgTop
  imports "AlgTopBase.AlgTop_JCT_Base"
begin

section \<open>*\<S>62 Invariance of Domain\<close>

text \<open>Lemma 62.2 (Borsuk lemma): if f: A \<rightarrow> S^2-{a,b} is continuous, injective, compact domain,
  and nulhomotopic, then a and b lie in the same component of S^2-f(A).\<close>

lemma Lemma_62_2_BorsukLemma:
  fixes A :: "'a set" and TA :: "'a set set" and f :: "'a \<Rightarrow> real \<times> real \<times> real"
    and a b :: "real \<times> real \<times> real"
  assumes hT: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hcomp: "top1_compact_on A TA"
      and ha: "a \<in> top1_S2" and hb: "b \<in> top1_S2" and hab: "a \<noteq> b"
      and hf: "top1_continuous_map_on A TA
             (top1_S2 - {a, b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})) f"
      and hinj: "inj_on f A"
      and hnul: "top1_nulhomotopic_on A TA
             (top1_S2 - {a, b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})) f"
  shows "\<exists>C. C \<in> top1_components_on (top1_S2 - f ` A)
         (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))
         \<and> a \<in> C \<and> b \<in> C"
  sorry \<comment> \<open>Munkres Lemma 62.2: Converse of Lemma 61.2 under injectivity.
     Proof: By Lemma 61.2's contrapositive + injectivity.
     If a,b NOT in same component, then f NOT nulhomotopic (by converse of 61.2).
     But f IS nulhomotopic. Contradiction.
     Actually: 61.2 says same_component \<Rightarrow> nulhomotopic.
     62.2 says nulhomotopic + injective \<Rightarrow> same_component.
     The proof of 62.2 in Munkres uses a retraction argument.\<close>

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

\<comment> \<open>top1_simple_closed_curve_on defined earlier (before \<S>61).\<close>

\<comment> \<open>Helix covering construction: provides E, TE, p0 for both 63.1(a) and g-lift.\<close>
lemma helix_covering_construction:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
  defines "E \<equiv> {(x::('a \<times> int)). (even (snd x) \<and> fst x \<in> U) \<or> (odd (snd x) \<and> fst x \<in> V - U)}"
  defines "TE \<equiv> {W. W \<subseteq> E \<and>
        (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
        (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
  defines "p0 \<equiv> (fst :: ('a \<times> int) \<Rightarrow> 'a)"
  shows "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
proof -
    have hU_TX: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
    have hV_TX: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
    have hA_TX: "A \<in> TX" using assms(7) unfolding openin_on_def by (by100 blast)
    have hB_TX: "B \<in> TX" using assms(8) unfolding openin_on_def by (by100 blast)
    have hAB: "A \<union> B = U \<inter> V" using assms(5) by simp
    have hTX_empty: "{} \<in> TX" using assms(1) unfolding is_topology_on_def by (by100 blast)
    have hTE: "is_topology_on E TE"
      unfolding is_topology_on_def
    proof (intro conjI allI impI)
      show "{} \<in> TE" unfolding TE_def using hTX_empty by simp
      show "E \<in> TE" unfolding TE_def
      proof (intro CollectI conjI allI)
        show "E \<subseteq> E" by simp
        fix n :: int
        show "{x \<in> U. (x, 2*n) \<in> E} \<in> TX"
          unfolding E_def using hU_TX by auto
        have "{x \<in> A. (x, 2*n+2) \<in> E} = A"
          unfolding E_def using hAB by auto
        moreover have "{x \<in> B. (x, 2*n) \<in> E} = B"
          unfolding E_def using hAB by auto
        moreover have "{x \<in> V-U. (x, 2*n+1) \<in> E} = V - U"
          unfolding E_def by auto
        moreover have "A \<union> B \<union> (V - U) = V" using hAB by (by100 blast)
        ultimately show "{x \<in> A. (x, 2*n+2) \<in> E} \<union> {x \<in> B. (x, 2*n) \<in> E} \<union> {x \<in> V-U. (x, 2*n+1) \<in> E} \<in> TX"
          using hV_TX by simp
      qed
    next
      fix U0 :: "('a \<times> int) set set" assume hU0: "U0 \<subseteq> TE"
      show "\<Union>U0 \<in> TE" unfolding TE_def
      proof (intro CollectI conjI allI)
        show "\<Union>U0 \<subseteq> E" using hU0 unfolding TE_def by (by100 blast)
        fix n :: int
        have heven_eq: "{x \<in> U. (x, 2*n) \<in> \<Union>U0} = \<Union>{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> U0}"
          by (by100 blast)
        have "{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> U0} \<subseteq> TX"
          using hU0 unfolding TE_def by (by100 blast)
        hence "\<Union>{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> U0} \<in> TX"
          using assms(1) unfolding is_topology_on_def by (by100 blast)
        thus "{x \<in> U. (x, 2*n) \<in> \<Union>U0} \<in> TX" using heven_eq by simp
        have hodd_eq: "{x \<in> A. (x, 2*n+2) \<in> \<Union>U0} \<union> {x \<in> B. (x, 2*n) \<in> \<Union>U0} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> \<Union>U0}
            = \<Union>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> U0}" by (by100 blast)
        have "{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> U0} \<subseteq> TX"
          using hU0 unfolding TE_def by (by100 blast)
        hence "\<Union>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> U0} \<in> TX"
          using assms(1) unfolding is_topology_on_def by (by100 blast)
        thus "{x \<in> A. (x, 2*n+2) \<in> \<Union>U0} \<union> {x \<in> B. (x, 2*n) \<in> \<Union>U0} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> \<Union>U0} \<in> TX" using hodd_eq by simp
      qed
    next
      fix F :: "('a \<times> int) set set" assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> TE"
      show "\<Inter>F \<in> TE" unfolding TE_def
      proof (intro CollectI conjI allI)
        show "\<Inter>F \<subseteq> E" using hF unfolding TE_def by (by100 blast)
        fix n :: int
        have "{x \<in> U. (x, 2*n) \<in> \<Inter>F} = \<Inter>{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F}"
          using hF by (by100 blast)
        moreover have "... \<in> TX"
        proof -
          have "finite {{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F}" using hF by simp
          moreover have "{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F} \<noteq> {}" using hF by (by100 blast)
          moreover have "{{x \<in> U. (x, 2*n) \<in> W} | W. W \<in> F} \<subseteq> TX"
            using hF unfolding TE_def by (by100 blast)
          ultimately show ?thesis using assms(1) unfolding is_topology_on_def by (by100 blast)
        qed
        ultimately show "{x \<in> U. (x, 2*n) \<in> \<Inter>F} \<in> TX" by simp
        have heq: "{x \<in> A. (x, 2*n+2) \<in> \<Inter>F} \<union> {x \<in> B. (x, 2*n) \<in> \<Inter>F} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F}
            = \<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> A. (x, 2*n+2) \<in> \<Inter>F} \<union> {x \<in> B. (x, 2*n) \<in> \<Inter>F} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F}"
          thus "x \<in> \<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F}" by (by100 blast)
        next
          fix x assume hx: "x \<in> \<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F}"
          from hF obtain W0 where "W0 \<in> F" by (by100 blast)
          hence "x \<in> {x \<in> A. (x, 2*n+2) \<in> W0} \<union> {x \<in> B. (x, 2*n) \<in> W0} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W0}" using hx by (by100 blast)
          hence "x \<in> A \<or> x \<in> B \<or> x \<in> V - U" by (by100 blast)
          thus "x \<in> {x \<in> A. (x, 2*n+2) \<in> \<Inter>F} \<union> {x \<in> B. (x, 2*n) \<in> \<Inter>F} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F}"
            using hx hAB assms(6) by (by100 blast)
        qed
        have "\<Inter>{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F} \<in> TX"
        proof -
          have "finite {{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F}" using hF by simp
          moreover have "{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F} \<noteq> {}" using hF by (by100 blast)
          moreover have "{{x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} | W. W \<in> F} \<subseteq> TX"
            using hF unfolding TE_def by (by100 blast)
          ultimately show ?thesis using assms(1) unfolding is_topology_on_def by (by100 blast)
        qed
        thus "{x \<in> A. (x, 2*n+2) \<in> \<Inter>F} \<union> {x \<in> B. (x, 2*n) \<in> \<Inter>F} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> \<Inter>F} \<in> TX" using heq by simp
      qed
    qed
    have hcov: "top1_covering_map_on E TE X TX p0"
      unfolding top1_covering_map_on_def
    proof (intro conjI)
      show "top1_continuous_map_on E TE X TX p0"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix e assume "e \<in> E"
        thus "p0 e \<in> X" unfolding p0_def E_def using assms(2,3,4) unfolding openin_on_def by auto
      next
        fix W assume hW: "W \<in> TX"
        show "{e \<in> E. p0 e \<in> W} \<in> TE" unfolding TE_def
        proof (intro CollectI conjI allI)
          show "{e \<in> E. p0 e \<in> W} \<subseteq> E" by (by100 blast)
          fix n :: int
          have "{x \<in> U. (x, 2*n) \<in> {e \<in> E. p0 e \<in> W}} = U \<inter> W"
            unfolding p0_def E_def by auto
          thus "{x \<in> U. (x, 2*n) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
            using topology_inter_open[OF assms(1) hU_TX hW] by simp
          have h1: "{x \<in> A. (x, 2*n+2) \<in> {e \<in> E. p0 e \<in> W}} = A \<inter> W"
            unfolding p0_def E_def using hAB by auto
          have h2: "{x \<in> B. (x, 2*n) \<in> {e \<in> E. p0 e \<in> W}} = B \<inter> W"
            unfolding p0_def E_def using hAB by auto
          have h3: "{x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. p0 e \<in> W}} = (V-U) \<inter> W"
            unfolding p0_def E_def by auto
          have "(A \<inter> W) \<union> (B \<inter> W) \<union> ((V-U) \<inter> W) = V \<inter> W" using hAB by (by100 blast)
          moreover have "V \<inter> W \<in> TX"
            by (rule topology_inter_open[OF assms(1) hV_TX hW])
          ultimately show "{x \<in> A. (x, 2*n+2) \<in> {e \<in> E. p0 e \<in> W}} \<union>
              {x \<in> B. (x, 2*n) \<in> {e \<in> E. p0 e \<in> W}} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
            using h1 h2 h3 by simp
        qed
      qed
    next
      show "p0 ` E = X"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> p0 ` E"
        thus "x \<in> X" unfolding p0_def E_def using assms(2,3,4) unfolding openin_on_def by auto
      next
        fix x assume "x \<in> X"
        hence "x \<in> U \<or> x \<in> V - U" using assms(4) by (by100 blast)
        thus "x \<in> p0 ` E"
        proof
          assume "x \<in> U"
          hence "(x, 0::int) \<in> E" unfolding E_def by simp
          thus ?thesis unfolding p0_def by (by100 force)
        next
          assume "x \<in> V - U"
          hence "(x, 1::int) \<in> E" unfolding E_def by simp
          thus ?thesis unfolding p0_def by (by100 force)
        qed
      qed
    next
      show "\<forall>b\<in>X. \<exists>Ub. b \<in> Ub \<and> top1_evenly_covered_on E TE X TX p0 Ub"
      proof
        fix b assume "b \<in> X"
        hence "b \<in> U \<or> b \<in> V - U" using assms(4) by (by100 blast)
        thus "\<exists>Ub. b \<in> Ub \<and> top1_evenly_covered_on E TE X TX p0 Ub"
        proof
          assume "b \<in> U"
          let ?\<V> = "(\<lambda>n::int. U \<times> {2*n}) ` UNIV"
          show ?thesis
          proof (intro exI[of _ U] conjI)
            show "b \<in> U" by (rule \<open>b \<in> U\<close>)
            show "top1_evenly_covered_on E TE X TX p0 U"
              unfolding top1_evenly_covered_on_def
            proof (intro conjI exI[of _ ?\<V>])
              show "openin_on X TX U" by (rule assms(2))
              \<comment> \<open>U-sheets open in TE.\<close>
              show "\<forall>V\<in>?\<V>. openin_on E TE V"
              proof
                fix Sn assume "Sn \<in> ?\<V>"
                then obtain k where hSn: "Sn = U \<times> {2*k}" by auto
                show "openin_on E TE Sn" unfolding openin_on_def
                proof (intro conjI)
                  show "Sn \<subseteq> E" unfolding hSn E_def by auto
                  show "Sn \<in> TE" unfolding TE_def hSn
                  proof (intro CollectI conjI allI)
                    show "U \<times> {2*k} \<subseteq> E" unfolding E_def by auto
                    fix m :: int
                    have "{x \<in> U. (x, 2*m) \<in> U \<times> {2*k}} = (if m = k then U else {})" by auto
                    thus "{x \<in> U. (x, 2*m) \<in> U \<times> {2*k}} \<in> TX"
                      using hU_TX hTX_empty by simp
                    have hA: "{x \<in> A. (x, 2*m+2) \<in> U \<times> {2*k}} = (if m+1=k then A else {})"
                      using hAB by auto
                    have hB: "{x \<in> B. (x, 2*m) \<in> U \<times> {2*k}} = (if m=k then B else {})"
                      using hAB by auto
                    have hVU: "{x \<in> V-U. (x, 2*m+1) \<in> U \<times> {2*k}} = {}" by auto
                    have hresult: "(if m+1=k then A else {}) \<union> (if m=k then B else {}) \<union> {} \<in> TX"
                    proof -
                      have "(if m+1=k then A else {}) \<in> TX" using hA_TX hTX_empty by simp
                      moreover have "(if m=k then B else {}) \<in> TX" using hB_TX hTX_empty by simp
                      moreover have "{} \<in> TX" by (rule hTX_empty)
                      ultimately have "{(if m+1=k then A else {}), (if m=k then B else {}), {}} \<subseteq> TX"
                        by (by100 blast)
                      hence "\<Union>{(if m+1=k then A else {}), (if m=k then B else {}), {}} \<in> TX"
                        using assms(1) unfolding is_topology_on_def by (by100 blast)
                      thus ?thesis by (by100 simp)
                    qed
                    have "{x \<in> A. (x, 2*m+2) \<in> U \<times> {2*k}} \<union>
                        {x \<in> B. (x, 2*m) \<in> U \<times> {2*k}} \<union>
                        {x \<in> V-U. (x, 2*m+1) \<in> U \<times> {2*k}}
                        = (if m+1=k then A else {}) \<union> (if m=k then B else {}) \<union> {}"
                      using hA hB hVU by presburger
                    thus "{x \<in> A. (x, 2*m+2) \<in> U \<times> {2*k}} \<union>
                        {x \<in> B. (x, 2*m) \<in> U \<times> {2*k}} \<union>
                        {x \<in> V-U. (x, 2*m+1) \<in> U \<times> {2*k}} \<in> TX"
                      using hresult by simp
                  qed
                qed
              qed
              show "\<forall>V\<in>?\<V>. \<forall>V'\<in>?\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" by force
              \<comment> \<open>Union = p0\<inverse>(U).\<close>
              show "{x \<in> E. p0 x \<in> U} = \<Union>?\<V>"
              proof (rule set_eqI, rule iffI)
                fix e assume "e \<in> {x \<in> E. p0 x \<in> U}"
                hence "e \<in> E" "fst e \<in> U" unfolding p0_def by auto
                hence "even (snd e)" unfolding E_def by auto
                then obtain k where "snd e = 2 * k" using evenE by auto
                hence "e \<in> U \<times> {2*k}" using \<open>fst e \<in> U\<close> by (cases e) auto
                thus "e \<in> \<Union>?\<V>" by (by100 blast)
              next
                fix e assume "e \<in> \<Union>?\<V>"
                then obtain n where "e \<in> U \<times> {2*n}" by (by100 blast)
                hence "e \<in> E" "p0 e \<in> U" unfolding E_def p0_def by auto
                thus "e \<in> {x \<in> E. p0 x \<in> U}" by simp
              qed
              \<comment> \<open>Sheet homeomorphisms.\<close>
              show "\<forall>V\<in>?\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                  (subspace_topology X TX U) p0"
              proof
                fix Sn assume "Sn \<in> ?\<V>"
                then obtain k where hSn: "Sn = U \<times> {2*k}" by auto
                have hSn_sub: "Sn \<subseteq> E" unfolding hSn E_def by auto
                have hU_sub: "U \<subseteq> X" using assms(2) unfolding openin_on_def by (by100 blast)
                show "top1_homeomorphism_on Sn (subspace_topology E TE Sn) U
                    (subspace_topology X TX U) p0"
                  unfolding top1_homeomorphism_on_def
                proof (intro conjI)
                  show "is_topology_on Sn (subspace_topology E TE Sn)"
                    by (rule subspace_topology_is_topology_on[OF hTE hSn_sub])
                  show "is_topology_on U (subspace_topology X TX U)"
                    by (rule subspace_topology_is_topology_on[OF assms(1) hU_sub])
                  show "bij_betw p0 Sn U" unfolding bij_betw_def p0_def hSn
                    by (intro conjI inj_onI, auto)
                  \<comment> \<open>p0 continuous.\<close>
                  show "top1_continuous_map_on Sn (subspace_topology E TE Sn) U
                      (subspace_topology X TX U) p0"
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix e assume "e \<in> Sn" thus "p0 e \<in> U" unfolding hSn p0_def by auto
                  next
                    fix W assume "W \<in> subspace_topology X TX U"
                    then obtain W0 where "W0 \<in> TX" "W = U \<inter> W0"
                      unfolding subspace_topology_def by (by100 blast)
                    define W' where "W' = {e \<in> E. p0 e \<in> W}"
                    have "W' \<in> TE" unfolding TE_def W'_def
                    proof (intro CollectI conjI allI)
                      show "{e \<in> E. p0 e \<in> W} \<subseteq> E" by (by100 blast)
                      fix m :: int
                      have hW_sub: "W \<subseteq> U" using \<open>W = U \<inter> W0\<close> by (by100 blast)
                      show "{x \<in> U. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
                      proof -
                        have "{x \<in> U. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} = U \<inter> W"
                          unfolding p0_def E_def by auto
                        moreover have "U \<inter> W = W" using hW_sub by (by100 blast)
                        moreover have "W \<in> TX"
                        proof -
                          have "U \<inter> W0 \<in> TX" by (rule topology_inter_open[OF assms(1) hU_TX \<open>W0 \<in> TX\<close>])
                          thus ?thesis using \<open>W = U \<inter> W0\<close> by simp
                        qed
                        ultimately show ?thesis by simp
                      qed
                      show "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                          {x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                          {x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
                      proof -
                        have h1: "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} = A \<inter> W"
                          unfolding p0_def E_def using hAB by auto
                        have h2: "{x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} = B \<inter> W"
                          unfolding p0_def E_def using hAB by auto
                        have h3: "{x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} = {}"
                          unfolding p0_def E_def using hW_sub by auto
                        have hW_TX: "W \<in> TX"
                        proof -
                          have "U \<inter> W0 \<in> TX" by (rule topology_inter_open[OF assms(1) hU_TX \<open>W0 \<in> TX\<close>])
                          thus ?thesis using \<open>W = U \<inter> W0\<close> by simp
                        qed
                        have "V \<inter> W \<in> TX" by (rule topology_inter_open[OF assms(1) hV_TX hW_TX])
                        moreover have "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                            {x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                            {x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} = V \<inter> W"
                        proof -
                          have "(A \<inter> W) \<union> (B \<inter> W) \<union> {} = V \<inter> W"
                            using hAB hW_sub by (by100 blast)
                          thus ?thesis using h1 h2 h3 by presburger
                        qed
                        ultimately show ?thesis by simp
                      qed
                    qed
                    moreover have "{e \<in> Sn. p0 e \<in> W} = Sn \<inter> W'"
                      unfolding W'_def using hSn_sub by (by100 blast)
                    ultimately show "{e \<in> Sn. p0 e \<in> W} \<in> subspace_topology E TE Sn"
                      unfolding subspace_topology_def by (by100 blast)
                  qed
                  \<comment> \<open>Inverse continuous.\<close>
                  show "top1_continuous_map_on U (subspace_topology X TX U) Sn
                      (subspace_topology E TE Sn) (inv_into Sn p0)"
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix x assume "x \<in> U"
                    have "inv_into Sn p0 x = (x, 2*k)"
                    proof (rule inv_into_f_eq)
                      show "inj_on p0 Sn" unfolding p0_def hSn by (intro inj_onI) auto
                      show "(x, 2*k) \<in> Sn" unfolding hSn using \<open>x \<in> U\<close> by simp
                      show "p0 (x, 2*k) = x" unfolding p0_def by simp
                    qed
                    thus "inv_into Sn p0 x \<in> Sn" unfolding hSn using \<open>x \<in> U\<close> by simp
                  next
                    fix W assume "W \<in> subspace_topology E TE Sn"
                    then obtain W' where "W' \<in> TE" "W = Sn \<inter> W'"
                      unfolding subspace_topology_def by (by100 blast)
                    have hinj: "inj_on p0 Sn" unfolding p0_def hSn by (intro inj_onI) auto
                    have hslice: "{x \<in> U. (x, 2*k) \<in> W'} \<in> TX"
                    proof -
                      have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W'} \<in> TX"
                        using \<open>W' \<in> TE\<close> unfolding TE_def by (by100 blast)
                      hence "{x \<in> U. (x, 2*k) \<in> W'} \<in> TX" by (rule spec)
                      thus ?thesis .
                    qed
                    have "{x \<in> U. inv_into Sn p0 x \<in> W} = {x \<in> U. (x, 2*k) \<in> W'}"
                    proof (rule set_eqI, rule iffI)
                      fix x assume "x \<in> {x \<in> U. inv_into Sn p0 x \<in> W}"
                      hence "x \<in> U" "inv_into Sn p0 x \<in> W" by auto
                      have "inv_into Sn p0 x = (x, 2*k)"
                        by (rule inv_into_f_eq[OF hinj]) (simp_all add: hSn p0_def \<open>x \<in> U\<close>)
                      thus "x \<in> {x \<in> U. (x, 2*k) \<in> W'}"
                        using \<open>inv_into Sn p0 x \<in> W\<close> \<open>W = Sn \<inter> W'\<close> hSn \<open>x \<in> U\<close> by auto
                    next
                      fix x assume "x \<in> {x \<in> U. (x, 2*k) \<in> W'}"
                      hence "x \<in> U" "(x, 2*k) \<in> W'" by auto
                      have "inv_into Sn p0 x = (x, 2*k)"
                        by (rule inv_into_f_eq[OF hinj]) (simp_all add: hSn p0_def \<open>x \<in> U\<close>)
                      have "inv_into Sn p0 x \<in> W'"
                        using \<open>inv_into Sn p0 x = (x, 2*k)\<close> \<open>(x, 2*k) \<in> W'\<close> by simp
                      moreover have "inv_into Sn p0 x \<in> Sn"
                        using \<open>inv_into Sn p0 x = (x, 2*k)\<close> hSn \<open>x \<in> U\<close> by simp
                      ultimately have "inv_into Sn p0 x \<in> W"
                        using \<open>W = Sn \<inter> W'\<close> by (by100 blast)
                      thus "x \<in> {x \<in> U. inv_into Sn p0 x \<in> W}" using \<open>x \<in> U\<close> by simp
                    qed
                    moreover have "{x \<in> U. (x, 2*k) \<in> W'} \<in> subspace_topology X TX U"
                      using hslice unfolding subspace_topology_def by (by100 blast)
                    ultimately show "{x \<in> U. inv_into Sn p0 x \<in> W} \<in> subspace_topology X TX U"
                      by simp
                  qed
                qed
              qed
            qed
          qed
        next
          assume "b \<in> V - U"
          \<comment> \<open>V evenly covered. V-sheets defined via vsheet.\<close>
          define vsheet :: "int \<Rightarrow> ('a \<times> int) set" where
            "vsheet = (\<lambda>n. {e \<in> E. fst e \<in> V \<and>
              (fst e \<in> A \<and> snd e = 2*(n+1) \<or> fst e \<in> B \<and> snd e = 2*n \<or> fst e \<in> V - U \<and> snd e = 2*n+1)})"
          let ?\<V>V = "vsheet ` UNIV"
          show ?thesis
          proof (intro exI[of _ V] conjI)
            show "b \<in> V" using \<open>b \<in> V - U\<close> by (by100 blast)
            show "top1_evenly_covered_on E TE X TX p0 V"
              unfolding top1_evenly_covered_on_def
            proof (intro conjI exI[of _ ?\<V>V])
              show "openin_on X TX V" by (rule assms(3))
              show hVsheets_open: "\<forall>Vn\<in>?\<V>V. openin_on E TE Vn"
              proof
                fix Sn assume "Sn \<in> ?\<V>V"
                then obtain k where hSn: "Sn = vsheet k" by (by100 blast)
                show "openin_on E TE Sn" unfolding openin_on_def
                proof (intro conjI)
                  show "Sn \<subseteq> E" unfolding hSn vsheet_def by (by100 blast)
                  show "Sn \<in> TE" unfolding TE_def hSn
                  proof (intro CollectI conjI allI)
                    show "vsheet k \<subseteq> E" unfolding vsheet_def by (by100 blast)
                    fix m :: int
                    \<comment> \<open>Even slice: {x \<in> U. (x,2m) \<in> vsheet k} = A if m=k+1, B if m=k, else {}.\<close>
                    have heven: "{x \<in> U. (x, 2*m) \<in> vsheet k} =
                        (if m = k+1 then A else if m = k then B else {})"
                      unfolding vsheet_def E_def using hAB assms(6) by auto
                    show "{x \<in> U. (x, 2*m) \<in> vsheet k} \<in> TX"
                    proof -
                      have "(if m=k+1 then A else if m=k then B else {}) \<in> TX"
                        using hA_TX hB_TX hTX_empty by simp
                      thus ?thesis using heven by simp
                    qed
                    \<comment> \<open>Odd slice: at m=k gives V, else {}.\<close>
                    have hodd_A: "{x \<in> A. (x, 2*m+2) \<in> vsheet k} = (if m=k then A else {})"
                      unfolding vsheet_def E_def using hAB assms(6) by auto
                    have hodd_B: "{x \<in> B. (x, 2*m) \<in> vsheet k} = (if m=k then B else {})"
                      unfolding vsheet_def E_def using hAB assms(6) by auto
                    have hodd_VU: "{x \<in> V-U. (x, 2*m+1) \<in> vsheet k} = (if m=k then V-U else {})"
                      unfolding vsheet_def E_def by auto
                    have hodd_eq: "(if m=k then A else {}) \<union> (if m=k then B else {}) \<union>
                        (if m=k then V-U else {}) = (if m=k then V else {})"
                      using hAB by auto
                    show "{x \<in> A. (x, 2*m+2) \<in> vsheet k} \<union>
                        {x \<in> B. (x, 2*m) \<in> vsheet k} \<union>
                        {x \<in> V-U. (x, 2*m+1) \<in> vsheet k} \<in> TX"
                    proof -
                      have "(if m=k then V else {}) \<in> TX" using hV_TX hTX_empty by simp
                      thus ?thesis using hodd_A hodd_B hodd_VU hodd_eq by presburger
                    qed
                  qed
                qed
              qed
              show "\<forall>Vn\<in>?\<V>V. \<forall>Vn'\<in>?\<V>V. Vn \<noteq> Vn' \<longrightarrow> Vn \<inter> Vn' = {}"
              proof (intro ballI impI)
                fix S1 S2 assume "S1 \<in> ?\<V>V" "S2 \<in> ?\<V>V" "S1 \<noteq> S2"
                then obtain n1 n2 where hS: "S1 = vsheet n1" "S2 = vsheet n2" by (by100 blast)
                have "n1 \<noteq> n2" using \<open>S1 \<noteq> S2\<close> hS by auto
                show "S1 \<inter> S2 = {}"
                proof (rule ccontr)
                  assume "S1 \<inter> S2 \<noteq> {}"
                  then obtain e where "e \<in> S1" "e \<in> S2" by (by100 blast)
                  hence "fst e \<in> A \<and> snd e = 2*(n1+1) \<or> fst e \<in> B \<and> snd e = 2*n1 \<or>
                      fst e \<in> V-U \<and> snd e = 2*n1+1"
                    "fst e \<in> A \<and> snd e = 2*(n2+1) \<or> fst e \<in> B \<and> snd e = 2*n2 \<or>
                      fst e \<in> V-U \<and> snd e = 2*n2+1"
                    unfolding hS vsheet_def by auto
                  thus False using \<open>n1 \<noteq> n2\<close> assms(6) hAB by auto
                qed
              qed
              show "{x \<in> E. p0 x \<in> V} = \<Union>?\<V>V"
              proof (rule set_eqI, rule iffI)
                fix e assume "e \<in> {x \<in> E. p0 x \<in> V}"
                hence he: "e \<in> E" "fst e \<in> V" unfolding p0_def by auto
                have "fst e \<in> A \<or> fst e \<in> B \<or> fst e \<in> V - U" using he(2) hAB by (by100 blast)
                thus "e \<in> \<Union>?\<V>V"
                proof (elim disjE)
                  assume "fst e \<in> A"
                  hence "even (snd e)" using he(1) unfolding E_def using hAB by auto
                  then obtain k where "snd e = 2 * k" using evenE by auto
                  have "e \<in> vsheet (k - 1)" unfolding vsheet_def
                    using he \<open>fst e \<in> A\<close> \<open>snd e = 2*k\<close> by (cases e) auto
                  thus ?thesis by (by100 blast)
                next
                  assume "fst e \<in> B"
                  hence "even (snd e)" using he(1) unfolding E_def using hAB by auto
                  then obtain k where "snd e = 2 * k" using evenE by auto
                  have "e \<in> vsheet k" unfolding vsheet_def
                    using he \<open>fst e \<in> B\<close> \<open>snd e = 2*k\<close> by (cases e) auto
                  thus ?thesis by (by100 blast)
                next
                  assume "fst e \<in> V - U"
                  hence "odd (snd e)" using he(1) unfolding E_def by auto
                  then obtain k where "snd e = 2 * k + 1" using oddE by auto
                  have "e \<in> vsheet k" unfolding vsheet_def
                    using he \<open>fst e \<in> V - U\<close> \<open>snd e = 2*k+1\<close> by (cases e) auto
                  thus ?thesis by (by100 blast)
                qed
              next
                fix e assume "e \<in> \<Union>?\<V>V"
                then obtain n where "e \<in> vsheet n" by (by100 blast)
                hence "e \<in> E" "fst e \<in> V" unfolding vsheet_def by auto
                thus "e \<in> {x \<in> E. p0 x \<in> V}" unfolding p0_def by simp
              qed
              show "\<forall>Vn\<in>?\<V>V. top1_homeomorphism_on Vn (subspace_topology E TE Vn) V
                  (subspace_topology X TX V) p0"
              proof
                fix Sn assume "Sn \<in> ?\<V>V"
                then obtain k where hSn: "Sn = vsheet k" by (by100 blast)
                have hSn_sub: "Sn \<subseteq> E" unfolding hSn vsheet_def by (by100 blast)
                have hV_sub: "V \<subseteq> X" using assms(3) unfolding openin_on_def by (by100 blast)
                have hbij: "bij_betw p0 Sn V" unfolding bij_betw_def
                proof (intro conjI)
                  show "inj_on p0 Sn" unfolding p0_def hSn
                  proof (intro inj_onI)
                    fix e1 e2 assume he1: "e1 \<in> vsheet k" and he2: "e2 \<in> vsheet k"
                        and hfst: "fst e1 = fst e2"
                    have h1: "fst e1 \<in> A \<and> snd e1 = 2*(k+1) \<or> fst e1 \<in> B \<and> snd e1 = 2*k \<or>
                        fst e1 \<in> V-U \<and> snd e1 = 2*k+1"
                      using he1 unfolding vsheet_def by auto
                    have h2: "fst e2 \<in> A \<and> snd e2 = 2*(k+1) \<or> fst e2 \<in> B \<and> snd e2 = 2*k \<or>
                        fst e2 \<in> V-U \<and> snd e2 = 2*k+1"
                      using he2 unfolding vsheet_def by auto
                    have "snd e1 = snd e2" using h1 h2 hfst assms(6) hAB by auto
                    thus "e1 = e2" using hfst by (cases e1, cases e2) auto
                  qed
                  show "p0 ` Sn = V"
                  proof (rule set_eqI, rule iffI)
                    fix x assume "x \<in> p0 ` Sn"
                    thus "x \<in> V" unfolding p0_def hSn vsheet_def by auto
                  next
                    fix x assume "x \<in> V"
                    hence "x \<in> A \<or> x \<in> B \<or> x \<in> V - U" using hAB by (by100 blast)
                    thus "x \<in> p0 ` Sn"
                    proof (elim disjE)
                      assume "x \<in> A"
                      hence "(x, 2*(k+1)) \<in> vsheet k" unfolding vsheet_def E_def
                        using \<open>x \<in> V\<close> hAB by auto
                      thus ?thesis unfolding p0_def hSn by force
                    next
                      assume "x \<in> B"
                      hence "(x, 2*k) \<in> vsheet k" unfolding vsheet_def E_def
                        using \<open>x \<in> V\<close> hAB by auto
                      thus ?thesis unfolding p0_def hSn by force
                    next
                      assume "x \<in> V - U"
                      hence "(x, 2*k+1) \<in> vsheet k" unfolding vsheet_def E_def
                        using \<open>x \<in> V\<close> by auto
                      thus ?thesis unfolding p0_def hSn by force
                    qed
                  qed
                qed
                have hp0_img: "p0 ` Sn = V" using hbij unfolding bij_betw_def by (by100 blast)
                have hinj: "inj_on p0 Sn" using hbij unfolding bij_betw_def by (by100 blast)
                show "top1_homeomorphism_on Sn (subspace_topology E TE Sn) V
                    (subspace_topology X TX V) p0"
                  unfolding top1_homeomorphism_on_def
                proof (intro conjI)
                  show "is_topology_on Sn (subspace_topology E TE Sn)"
                    by (rule subspace_topology_is_topology_on[OF hTE hSn_sub])
                  show "is_topology_on V (subspace_topology X TX V)"
                    by (rule subspace_topology_is_topology_on[OF assms(1) hV_sub])
                  show "bij_betw p0 Sn V" by (rule hbij)
                  \<comment> \<open>p0 continuous: preimage of TX-open in V = TE-open in Sn.\<close>
                  show "top1_continuous_map_on Sn (subspace_topology E TE Sn) V
                      (subspace_topology X TX V) p0"
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix e assume "e \<in> Sn"
                    thus "p0 e \<in> V" unfolding hSn p0_def vsheet_def by auto
                  next
                    fix W assume "W \<in> subspace_topology X TX V"
                    then obtain W0 where hW0: "W0 \<in> TX" "W = V \<inter> W0"
                      unfolding subspace_topology_def by (by100 blast)
                    have hW_sub: "W \<subseteq> V" using hW0 by (by100 blast)
                    have hW_TX: "V \<inter> W0 \<in> TX"
                      by (rule topology_inter_open[OF assms(1) hV_TX hW0(1)])
                    hence hW_in_TX: "W \<in> TX" using hW0 by simp
                    \<comment> \<open>Build W' \<in> TE with Sn \<inter> W' = {e \<in> Sn. p0 e \<in> W}.\<close>
                    define W' where "W' = {e \<in> E. p0 e \<in> W}"
                    have "W' \<in> TE" unfolding TE_def W'_def
                    proof (intro CollectI conjI allI)
                      show "{e \<in> E. p0 e \<in> W} \<subseteq> E" by (by100 blast)
                      fix m :: int
                      have "{x \<in> U. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} = U \<inter> W"
                        unfolding p0_def E_def by auto
                      thus "{x \<in> U. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
                        using topology_inter_open[OF assms(1) hU_TX hW_in_TX] by simp
                      have h1: "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} = A \<inter> W"
                        unfolding p0_def E_def using hAB by auto
                      have h2: "{x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} = B \<inter> W"
                        unfolding p0_def E_def using hAB by auto
                      have h3: "{x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} = (V-U) \<inter> W"
                        unfolding p0_def E_def using hW_sub by auto
                      have "(A\<inter>W) \<union> (B\<inter>W) \<union> ((V-U)\<inter>W) = V \<inter> W" using hAB by (by100 blast)
                      hence "... \<in> TX" using topology_inter_open[OF assms(1) hV_TX hW_in_TX] by simp
                      thus "{x \<in> A. (x, 2*m+2) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                          {x \<in> B. (x, 2*m) \<in> {e \<in> E. p0 e \<in> W}} \<union>
                          {x \<in> V-U. (x, 2*m+1) \<in> {e \<in> E. p0 e \<in> W}} \<in> TX"
                        using h1 h2 h3 \<open>(A\<inter>W) \<union> (B\<inter>W) \<union> ((V-U)\<inter>W) = V \<inter> W\<close> by presburger
                    qed
                    have "{e \<in> Sn. p0 e \<in> W} = Sn \<inter> W'"
                      unfolding W'_def using hSn_sub by (by100 blast)
                    thus "{e \<in> Sn. p0 e \<in> W} \<in> subspace_topology E TE Sn"
                      using \<open>W' \<in> TE\<close> unfolding subspace_topology_def by (by100 blast)
                  qed
                  \<comment> \<open>Inverse continuous: preimage under inv_into uses odd-slice of TE.\<close>
                  show "top1_continuous_map_on V (subspace_topology X TX V) Sn
                      (subspace_topology E TE Sn) (inv_into Sn p0)"
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix x assume "x \<in> V"
                    thus "inv_into Sn p0 x \<in> Sn" using hp0_img by (simp add: inv_into_into)
                  next
                    fix W assume "W \<in> subspace_topology E TE Sn"
                    then obtain W' where hW': "W' \<in> TE" "W = Sn \<inter> W'"
                      unfolding subspace_topology_def by (by100 blast)
                    have hslice: "{x \<in> A. (x, 2*k+2) \<in> W'} \<union> {x \<in> B. (x, 2*k) \<in> W'} \<union>
                        {x \<in> V-U. (x, 2*k+1) \<in> W'} \<in> TX"
                    proof -
                      have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W'} \<union> {x \<in> B. (x, 2*n) \<in> W'} \<union>
                          {x \<in> V-U. (x, 2*n+1) \<in> W'} \<in> TX"
                        using hW'(1) unfolding TE_def by (by100 blast)
                      hence "{x \<in> A. (x, 2*k+2) \<in> W'} \<union> {x \<in> B. (x, 2*k) \<in> W'} \<union>
                          {x \<in> V-U. (x, 2*k+1) \<in> W'} \<in> TX" by blast
                      thus ?thesis .
                    qed
                    \<comment> \<open>inv_into maps: x\<in>A \<mapsto> (x,2(k+1)), x\<in>B \<mapsto> (x,2k), x\<in>V\U \<mapsto> (x,2k+1).\<close>
                    have hinv_A: "\<And>x. x \<in> A \<Longrightarrow> x \<in> V \<Longrightarrow> inv_into Sn p0 x = (x, 2*(k+1))"
                    proof -
                      fix x assume "x \<in> A" "x \<in> V"
                      have "(x, 2*(k+1)) \<in> Sn" unfolding hSn vsheet_def E_def
                        using \<open>x \<in> A\<close> \<open>x \<in> V\<close> hAB by auto
                      thus "inv_into Sn p0 x = (x, 2*(k+1))"
                        by (intro inv_into_f_eq[OF hinj]) (simp_all add: p0_def)
                    qed
                    have hinv_B: "\<And>x. x \<in> B \<Longrightarrow> x \<in> V \<Longrightarrow> inv_into Sn p0 x = (x, 2*k)"
                    proof -
                      fix x assume "x \<in> B" "x \<in> V"
                      have "(x, 2*k) \<in> Sn" unfolding hSn vsheet_def E_def
                        using \<open>x \<in> B\<close> \<open>x \<in> V\<close> hAB by auto
                      thus "inv_into Sn p0 x = (x, 2*k)"
                        by (intro inv_into_f_eq[OF hinj]) (simp_all add: p0_def)
                    qed
                    have hinv_VU: "\<And>x. x \<in> V - U \<Longrightarrow> inv_into Sn p0 x = (x, 2*k+1)"
                    proof -
                      fix x assume "x \<in> V - U"
                      have "(x, 2*k+1) \<in> Sn" unfolding hSn vsheet_def E_def
                        using \<open>x \<in> V - U\<close> by auto
                      thus "inv_into Sn p0 x = (x, 2*k+1)"
                        by (intro inv_into_f_eq[OF hinj]) (simp_all add: p0_def)
                    qed
                    have hpre: "{x \<in> V. inv_into Sn p0 x \<in> W} =
                        {x \<in> A. (x, 2*(k+1)) \<in> W'} \<union> {x \<in> B. (x, 2*k) \<in> W'} \<union>
                        {x \<in> V-U. (x, 2*k+1) \<in> W'}"
                    proof (rule set_eqI, rule iffI)
                      fix x assume hx: "x \<in> {x \<in> V. inv_into Sn p0 x \<in> W}"
                      hence "x \<in> V" "inv_into Sn p0 x \<in> W'" "inv_into Sn p0 x \<in> Sn"
                        using hW'(2) hp0_img inv_into_into[of x p0 Sn] by auto
                      have "x \<in> A \<or> x \<in> B \<or> x \<in> V-U" using \<open>x \<in> V\<close> hAB by (by100 blast)
                      thus "x \<in> {x \<in> A. (x, 2*(k+1)) \<in> W'} \<union> {x \<in> B. (x, 2*k) \<in> W'} \<union>
                          {x \<in> V-U. (x, 2*k+1) \<in> W'}"
                      proof (elim disjE)
                        assume "x \<in> A"
                        thus ?thesis using hinv_A \<open>x \<in> V\<close> \<open>inv_into Sn p0 x \<in> W'\<close> by auto
                      next
                        assume "x \<in> B"
                        thus ?thesis using hinv_B \<open>x \<in> V\<close> \<open>inv_into Sn p0 x \<in> W'\<close> by auto
                      next
                        assume "x \<in> V - U"
                        thus ?thesis using hinv_VU \<open>inv_into Sn p0 x \<in> W'\<close> by auto
                      qed
                    next
                      fix x assume "x \<in> {x \<in> A. (x, 2*(k+1)) \<in> W'} \<union>
                          {x \<in> B. (x, 2*k) \<in> W'} \<union> {x \<in> V-U. (x, 2*k+1) \<in> W'}"
                      hence "x \<in> V" using hAB by (by100 blast)
                      have "inv_into Sn p0 x \<in> W'"
                        using \<open>x \<in> _ \<union> _ \<union> _\<close> hinv_A hinv_B hinv_VU \<open>x \<in> V\<close> by auto
                      moreover have "inv_into Sn p0 x \<in> Sn"
                        using \<open>x \<in> V\<close> hp0_img by (simp add: inv_into_into)
                      ultimately show "x \<in> {x \<in> V. inv_into Sn p0 x \<in> W}"
                        using \<open>x \<in> V\<close> hW'(2) by (by100 blast)
                    qed
                    have hpre_sub: "{x \<in> V. inv_into Sn p0 x \<in> W} \<subseteq> V" by (by100 blast)
                    have hpre_TX: "{x \<in> V. inv_into Sn p0 x \<in> W} \<in> TX"
                      using hpre hslice by simp
                    show "{x \<in> V. inv_into Sn p0 x \<in> W} \<in> subspace_topology X TX V"
                    proof -
                      have "{x \<in> V. inv_into Sn p0 x \<in> W} =
                          V \<inter> {x \<in> V. inv_into Sn p0 x \<in> W}" using hpre_sub by (by100 blast)
                      thus ?thesis using hpre_TX unfolding subspace_topology_def by (by100 blast)
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    show ?thesis using hTE hcov by simp
  qed

(** from \<S>63 Theorem 63.1: if X = U \<union> V with U \<inter> V = A \<union> B (disjoint open),
    and alpha: a to b in U, beta: b to a in V, then the loop f = alpha * beta is
    nontrivial in pi_1(X, a) (plus further properties: homotopy lifts, f^m and f^k
    are nonconjugate when the components are different). Used in Munkres' proof of
    the Jordan Curve Theorem. **)

theorem Theorem_63_1_loop_nontrivial:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
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
  \<comment> \<open>Step 1+2: Build covering space E (type 'a \<times> int) and lift f to get different endpoints.\<close>
  have "\<exists>(E::('a \<times> int) set) TE (p0::('a \<times> int) \<Rightarrow> 'a) e0 e1.
      top1_covering_map_on E TE X TX p0
    \<and> is_topology_on E TE
    \<and> e0 \<in> E \<and> p0 e0 = a
    \<and> e1 \<in> E \<and> p0 e1 = a
    \<and> e0 \<noteq> e1
    \<and> (\<exists>ftilde. top1_is_path_on E TE e0 e1 ftilde
        \<and> (\<forall>s\<in>I_set. p0 (ftilde s) = top1_path_product alpha beta s))"
  proof -
    \<comment> \<open>Helix covering: E = canonical representatives of quotient Y/~.
       E = {(x, 2n) | x \<in> U} \<union> {(x, 2n+1) | x \<in> V\U}. Covering map p = fst.\<close>
    have ha_X: "a \<in> X" using assms(4,5,9) by (by100 blast)
    have hb_X: "b \<in> X" using assms(4,5,10) by (by100 blast)
    have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
    have hb_U: "b \<in> U" using assms(5,10) by (by100 blast)
    have ha_V: "a \<in> V" using assms(5,9) by (by100 blast)
    have hb_V: "b \<in> V" using assms(5,10) by (by100 blast)
    have hU_open_TX: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
    have hV_open_TX: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
    have hA_open_TX: "A \<in> TX" using assms(7) unfolding openin_on_def by (by100 blast)
    have hB_open_TX: "B \<in> TX" using assms(8) unfolding openin_on_def by (by100 blast)
    have hAB_UV: "A \<union> B = U \<inter> V" using assms(5) by simp
    have hAB_disj: "A \<inter> B = {}" using assms(6) .
    \<comment> \<open>Define normalization: maps Y = \<Union>(U\<times>{2n}) \<union> \<Union>(V\<times>{2n+1}) to canonical reps.\<close>
    define norm :: "'a \<times> int \<Rightarrow> 'a \<times> int" where
      "norm = (\<lambda>(x, m). if even m then (x, m)
               else if x \<in> A then (x, m + 1)
               else if x \<in> B then (x, m - 1)
               else (x, m))"
    \<comment> \<open>Define E = set of canonical representatives.\<close>
    define E :: "('a \<times> int) set" where
      "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
    \<comment> \<open>Define quotient topology on E.\<close>
    define TE :: "('a \<times> int) set set" where
      "TE = {W. W \<subseteq> E \<and>
        (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
        (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
    define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
    define e0 :: "'a \<times> int" where "e0 = (a, 0)"
    define e1 :: "'a \<times> int" where "e1 = (a, 2)"
    \<comment> \<open>Basic facts about e0, e1.\<close>
    have he0_E: "e0 \<in> E" unfolding e0_def E_def using ha_U by simp
    have he1_E: "e1 \<in> E" unfolding e1_def E_def using ha_U by simp
    have hp0e0: "p0 e0 = a" unfolding p0_def e0_def by simp
    have hp0e1: "p0 e1 = a" unfolding p0_def e1_def by simp
    have hne: "e0 \<noteq> e1" unfolding e0_def e1_def by simp
    \<comment> \<open>TE is a topology on E, and p0 is a covering map. Use shared lemma.\<close>
    have hcov_and_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
    proof -
      note h = helix_covering_construction[OF assms(1-8)]
      have hE_eq: "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
        unfolding E_def by auto
      have hTE_eq: "TE = {W. W \<subseteq> E \<and>
          (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
          (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
                {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
        unfolding TE_def E_def by auto
      have hp0_eq: "p0 = fst" unfolding p0_def by simp
      show ?thesis using h hE_eq hTE_eq hp0_eq by simp
    qed
    have hTE: "is_topology_on E TE" using hcov_and_TE by simp
    have hcov: "top1_covering_map_on E TE X TX p0" using hcov_and_TE by simp
    \<comment> \<open>The TE topology and covering map proofs (previously ~687 lines inline)
       are now in helix_covering_construction. The old proofs are removed.\<close>
    \<comment> \<open>Define the lift: \<alpha>-tilde on [0,1/2] maps to (alpha(2s), 0).
       \<beta>-tilde on [1/2,1] maps to norm(\<beta>(2s-1), 1).\<close>
    define ftilde :: "real \<Rightarrow> ('a \<times> int)" where
      "ftilde = (\<lambda>s. if s \<le> 1/2
        then (alpha (2*s), 0)
        else (let y = beta (2*s - 1) in
              if y \<in> A then (y, 2)
              else if y \<in> B then (y, 0)
              else (y, 1)))"
    \<comment> \<open>Lift is a path from e0 to e1.\<close>
    have hft_path: "top1_is_path_on E TE e0 e1 ftilde"
    proof -
      \<comment> \<open>ftilde = path_product of \<alpha>-lift and \<beta>-lift. Use path product.\<close>
      define \<alpha>_lift where "\<alpha>_lift = (\<lambda>s. (alpha s, 0::int))"
      define \<beta>_lift where "\<beta>_lift = (\<lambda>s. let y = beta s in
        if y \<in> A then (y, 2::int) else if y \<in> B then (y, 0::int) else (y, 1::int))"
      have hft_eq: "ftilde = top1_path_product \<alpha>_lift \<beta>_lift"
        unfolding ftilde_def top1_path_product_def \<alpha>_lift_def \<beta>_lift_def by (rule ext) auto
      \<comment> \<open>\<alpha>_lift: path from (a,0) to (b,0) in U-sheet 0.\<close>
      have h\<alpha>_lift_path: "top1_is_path_on E TE (a, 0) (b, 0) \<alpha>_lift"
      proof -
        \<comment> \<open>\<alpha> is a path in U. The U-sheet S0 = U \<times> {0} is open in E, and
           p0|S0: S0 \<rightarrow> U is a homeomorphism. The inverse sends x to (x, 0).
           So \<alpha>_lift = inv(p0|S0) \<circ> \<alpha> is continuous.\<close>
        have hS0: "U \<times> {0::int} \<subseteq> E" unfolding E_def by auto
        \<comment> \<open>\<alpha> is continuous from I to U with subspace topology from TX.\<close>
        have h\<alpha>_path_U: "top1_is_path_on U (subspace_topology X TX U) a b alpha"
          by (rule assms(11))
        \<comment> \<open>\<alpha>_lift = (\<lambda>s. (alpha s, 0)). Continuous because: for each open W \<in> TE,
           {s \<in> I | \<alpha>_lift s \<in> W} = {s \<in> I | alpha s \<in> {x \<in> U. (x,0) \<in> W}}.
           And {x \<in> U. (x,0) \<in> W} is open in TX (from TE definition, even slice).
           So this is open in I (since \<alpha> is continuous).\<close>
        show ?thesis unfolding top1_is_path_on_def
        proof (intro conjI)
          show "top1_continuous_map_on I_set I_top E TE \<alpha>_lift"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set"
            hence "alpha s \<in> U" using h\<alpha>_path_U
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "\<alpha>_lift s \<in> E" unfolding \<alpha>_lift_def E_def by auto
          next
            fix W assume hW: "W \<in> TE"
            \<comment> \<open>Need {s \<in> I. \<alpha>_lift s \<in> W} \<in> I_top.\<close>
            have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
            proof -
              have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
              hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
              thus ?thesis by simp
            qed
            have heq: "{s \<in> I_set. \<alpha>_lift s \<in> W} = {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            proof (rule set_eqI, rule iffI)
              fix s assume "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}"
              hence "s \<in> I_set" "\<alpha>_lift s \<in> W" by auto
              hence "alpha s \<in> U" "(alpha s, 0::int) \<in> W"
                using h\<alpha>_path_U unfolding top1_is_path_on_def top1_continuous_map_on_def
                  \<alpha>_lift_def by auto
              thus "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
                using \<open>s \<in> I_set\<close> by (by100 blast)
            next
              fix s assume "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
              hence "s \<in> I_set" "alpha s \<in> U" "(alpha s, 0::int) \<in> W" by auto
              thus "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}" unfolding \<alpha>_lift_def by simp
            qed
            \<comment> \<open>The slice {x \<in> U. (x,0) \<in> W} is TX-open. It's also a subset of U,
               so it's open in the subspace topology of U from TX.
               \<alpha> continuous from I to U means preimage of this set is I_top-open.\<close>
            have hslice_U: "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
            proof -
              have "{x \<in> U. (x, 0::int) \<in> W} \<subseteq> U" by (by100 blast)
              hence "{x \<in> U. (x, 0::int) \<in> W} = U \<inter> {x \<in> U. (x, 0::int) \<in> W}" by (by100 blast)
              thus ?thesis using hslice unfolding subspace_topology_def by (by100 blast)
            qed
            have "{s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
              using h\<alpha>_path_U hslice_U
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "{s \<in> I_set. \<alpha>_lift s \<in> W} \<in> I_top" using heq by simp
          qed
          show "\<alpha>_lift 0 = (a, 0::int)"
            unfolding \<alpha>_lift_def using assms(11)
            unfolding top1_is_path_on_def by simp
          show "\<alpha>_lift 1 = (b, 0::int)"
            unfolding \<alpha>_lift_def using assms(11)
            unfolding top1_is_path_on_def by simp
        qed
      qed
      \<comment> \<open>\<beta>_lift: path from (b,0) to (a,2) in E.\<close>
      have h\<beta>_lift_path: "top1_is_path_on E TE (b, 0) (a, 2) \<beta>_lift"
      proof -
        have h\<beta>_path_V: "top1_is_path_on V (subspace_topology X TX V) b a beta"
          by (rule assms(12))
        show ?thesis unfolding top1_is_path_on_def
        proof (intro conjI)
          show "top1_continuous_map_on I_set I_top E TE \<beta>_lift"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set"
            hence "beta s \<in> V" using h\<beta>_path_V
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "\<beta>_lift s \<in> E" unfolding \<beta>_lift_def E_def Let_def
              using hAB_UV hAB_disj by auto
          next
            fix W assume hW: "W \<in> TE"
            \<comment> \<open>{s \<in> I. \<beta>_lift s \<in> W}. For s with beta(s) \<in> A: \<beta>_lift s = (beta s, 2).
               For beta(s) \<in> B: (beta s, 0). For beta(s) \<in> V\U: (beta s, 1).
               The odd V-slice condition of TE gives:
               {x \<in> A. (x,2) \<in> W} \<union> {x \<in> B. (x,0) \<in> W} \<union> {x \<in> V\U. (x,1) \<in> W} \<in> TX.
               This is exactly the set {x \<in> V. \<beta>_lift_at x \<in> W} (the "V-slice" at level n=0).
               Since \<beta> is continuous from I to V, preimage is I_top-open.\<close>
            have hV_slice: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                {x \<in> V - U. (x, 1::int) \<in> W} \<in> TX"
            proof -
              have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX"
                using hW unfolding TE_def by (by100 blast)
              hence "{x \<in> A. (x, 2*(0::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(0::int)) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*(0::int)+1) \<in> W} \<in> TX" by (rule spec)
              thus ?thesis by simp
            qed
            have heq: "{s \<in> I_set. \<beta>_lift s \<in> W} =
                {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
                    {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
            proof (rule set_eqI, rule iffI)
              fix s assume hs: "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}"
              hence "s \<in> I_set" "\<beta>_lift s \<in> W" by auto
              have "beta s \<in> V" using \<open>s \<in> I_set\<close> h\<beta>_path_V
                unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
              hence "beta s \<in> A \<or> beta s \<in> B \<or> beta s \<in> V - U"
                using hAB_UV by (by100 blast)
              have "\<beta>_lift s \<in> W" by (rule \<open>\<beta>_lift s \<in> W\<close>)
              have "beta s \<in> {x \<in> A. (x, 2::int) \<in> W} \<union>
                  {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W}"
              proof -
                have "beta s \<in> A \<or> beta s \<in> B \<or> beta s \<in> V - U" by (rule \<open>beta s \<in> A \<or> _\<close>)
                thus ?thesis
                proof (elim disjE)
                  assume "beta s \<in> A"
                  hence "\<beta>_lift s = (beta s, 2::int)" unfolding \<beta>_lift_def Let_def by simp
                  hence "(beta s, 2::int) \<in> W" using \<open>\<beta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>beta s \<in> A\<close> by (by100 blast)
                next
                  assume "beta s \<in> B"
                  hence "\<beta>_lift s = (beta s, 0::int)" unfolding \<beta>_lift_def Let_def
                    using hAB_disj by auto
                  hence "(beta s, 0::int) \<in> W" using \<open>\<beta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>beta s \<in> B\<close> by (by100 blast)
                next
                  assume "beta s \<in> V - U"
                  hence "beta s \<notin> A" "beta s \<notin> B" using hAB_UV by (by100 blast)+
                  hence "\<beta>_lift s = (beta s, 1::int)" unfolding \<beta>_lift_def Let_def by auto
                  hence "(beta s, 1::int) \<in> W" using \<open>\<beta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>beta s \<in> V - U\<close> by (by100 blast)
                qed
              qed
              thus "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
                  {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
                using \<open>s \<in> I_set\<close> by (by100 blast)
            next
              fix s assume hs: "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
                  {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
              hence "s \<in> I_set" by simp
              from hs have hcases: "beta s \<in> A \<and> (beta s, 2::int) \<in> W \<or>
                  beta s \<in> B \<and> (beta s, 0::int) \<in> W \<or>
                  beta s \<in> V - U \<and> (beta s, 1::int) \<in> W" by (by100 blast)
              have "\<beta>_lift s \<in> W"
              proof -
                from hcases show ?thesis
                proof (elim disjE conjE)
                  assume "beta s \<in> A" "(beta s, 2::int) \<in> W"
                  hence "\<beta>_lift s = (beta s, 2::int)" unfolding \<beta>_lift_def Let_def by simp
                  thus ?thesis using \<open>(beta s, 2) \<in> W\<close> by simp
                next
                  assume "beta s \<in> B" "(beta s, 0::int) \<in> W"
                  hence "\<beta>_lift s = (beta s, 0::int)" unfolding \<beta>_lift_def Let_def
                    using hAB_disj by auto
                  thus ?thesis using \<open>(beta s, 0) \<in> W\<close> by simp
                next
                  assume "beta s \<in> V - U" "(beta s, 1::int) \<in> W"
                  hence "beta s \<notin> A" "beta s \<notin> B" using hAB_UV by (by100 blast)+
                  hence "\<beta>_lift s = (beta s, 1::int)" unfolding \<beta>_lift_def Let_def by auto
                  thus ?thesis using \<open>(beta s, 1) \<in> W\<close> by simp
                qed
              qed
              thus "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}" using \<open>s \<in> I_set\<close> by (by100 blast)
            qed
            have hV_sub_open: "{x \<in> A. (x, 2::int) \<in> W} \<union>
                {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W}
                \<in> subspace_topology X TX V"
            proof -
              have hsub: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                  {x \<in> V - U. (x, 1::int) \<in> W} \<subseteq> V" using hAB_UV by (by100 blast)
              hence "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                  {x \<in> V - U. (x, 1::int) \<in> W} =
                  V \<inter> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                      {x \<in> V - U. (x, 1::int) \<in> W})" by (by100 blast)
              thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
            qed
            have "{s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
                {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})} \<in> I_top"
              using h\<beta>_path_V hV_sub_open
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "{s \<in> I_set. \<beta>_lift s \<in> W} \<in> I_top" using heq by simp
          qed
          show "\<beta>_lift 0 = (b, 0::int)"
            unfolding \<beta>_lift_def Let_def using assms(12) assms(10) hAB_disj
            unfolding top1_is_path_on_def by auto
          show "\<beta>_lift 1 = (a, 2::int)"
            unfolding \<beta>_lift_def Let_def using assms(12) assms(9)
            unfolding top1_is_path_on_def by auto
        qed
      qed
      have hTX_E: "is_topology_on E TE" by (rule hTE)
      have "top1_is_path_on E TE (a, 0) (a, 2) (top1_path_product \<alpha>_lift \<beta>_lift)"
        by (rule top1_path_product_is_path[OF hTX_E h\<alpha>_lift_path h\<beta>_lift_path])
      thus ?thesis unfolding hft_eq e0_def e1_def .
    qed
    \<comment> \<open>Lift projects correctly.\<close>
    have hft_lift: "\<forall>s\<in>I_set. p0 (ftilde s) = top1_path_product alpha beta s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hs_range: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
      show "p0 (ftilde s) = top1_path_product alpha beta s"
      proof (cases "s \<le> 1/2")
        case True
        hence "ftilde s = (alpha (2*s), 0)" unfolding ftilde_def by simp
        hence "p0 (ftilde s) = alpha (2*s)" unfolding p0_def by simp
        moreover have "top1_path_product alpha beta s = alpha (2*s)"
          unfolding top1_path_product_def using True by simp
        ultimately show ?thesis by simp
      next
        case False
        hence hs_half: "s > 1/2" by simp
        have "p0 (ftilde s) = beta (2*s - 1)"
        proof -
          define y where "y = beta (2*s - 1)"
          have "ftilde s = (if y \<in> A then (y, 2) else if y \<in> B then (y, 0) else (y, 1))"
            unfolding ftilde_def y_def using hs_half by (simp add: Let_def)
          hence "p0 (ftilde s) = y" unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
          thus ?thesis unfolding y_def by simp
        qed
        moreover have "top1_path_product alpha beta s = beta (2*s - 1)"
          unfolding top1_path_product_def using False by simp
        ultimately show ?thesis by simp
      qed
    qed
    show ?thesis
      using hcov hTE he0_E he1_E hp0e0 hp0e1 hne hft_path hft_lift
      by (intro exI[of _ E] exI[of _ TE] exI[of _ p0] exI[of _ e0] exI[of _ e1])
         (by100 blast)
  qed
  \<comment> \<open>Step 3: If f were nulhomotopic, the lift would be a loop (same start and end).
     But we showed the lift has different endpoints. Contradiction.\<close>
  \<comment> \<open>From step 2, obtain covering E, map p0, points e0 \<noteq> e1, and lift ftilde.\<close>
  from this obtain E :: "('a \<times> int) set" and TE :: "('a \<times> int) set set"
      and p0 :: "('a \<times> int) \<Rightarrow> 'a"
      and e0 :: "'a \<times> int" and e1 :: "'a \<times> int"
      and ftilde :: "real \<Rightarrow> ('a \<times> int)" where
      hcov: "top1_covering_map_on E TE X TX p0"
      and hTE: "is_topology_on E TE"
      and he0: "e0 \<in> E" and hp0e0: "p0 e0 = a"
      and he1: "e1 \<in> E" and hp0e1: "p0 e1 = a"
      and hne: "e0 \<noteq> e1"
      and hft: "top1_is_path_on E TE e0 e1 ftilde"
      and hft_lift: "\<forall>s\<in>I_set. p0 (ftilde s) = top1_path_product alpha beta s"
    by (by100 blast)
  \<comment> \<open>hnul gives a homotopy from \<alpha>*\<beta> to const_a. Lift it via Lemma_54_2.\<close>
  \<comment> \<open>The lifted homotopy starts from lift of \<alpha>*\<beta> = ftilde (starts at e0),
     and ends at lift of const_a (starts at e0) = const_{e0}.
     By Theorem_54_3 (unique endpoints), ftilde(1) = const_{e0}(1) = e0.
     But ftilde(1) = e1 \<noteq> e0. Contradiction.\<close>
  \<comment> \<open>By Theorem_54_3: path-homotopic loops with same start lift to paths with same endpoint.\<close>
  have hfab_path: "top1_is_path_on X TX a a (top1_path_product alpha beta)"
    using hnul unfolding top1_path_homotopic_on_def by (by100 blast)
  have hca_path: "top1_is_path_on X TX a a (top1_constant_path a)"
    using hnul unfolding top1_path_homotopic_on_def by (by100 blast)
  \<comment> \<open>hTE already obtained from step 2.\<close>
  have hTX: "is_topology_on X TX" by (rule assms(1))
  have hconst_lift: "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
    by (rule top1_constant_path_is_path[OF hTE he0])
  have hconst_lifts: "\<forall>s\<in>I_set. p0 (top1_constant_path e0 s) = top1_constant_path a s"
    unfolding top1_constant_path_def using hp0e0 by simp
  have "e1 = e0"
    using conjunct1[OF Theorem_54_3[OF hcov hTE hTX he0 hp0e0
        hfab_path hca_path hnul hft hft_lift hconst_lift hconst_lifts]]
    by simp
  thus False using hne by simp
qed

\<comment> \<open>Theorem 63.1(c): In the helix covering, g = \<gamma>*\<delta> lifts to a LOOP at e0
   (because a, a' \<in> A: no sheet shift). Combined with f = \<alpha>*\<beta> lifting
   to a NON-loop (sheet shift by 2), this means:
   [f]^m = [g]^k \<Rightarrow> m = 0 (since lifts have endpoints (a,2m) vs (a,0)).
   For 63.5: this contradicts \<pi>_1(X) \<cong> Z (rank 1 \<Rightarrow> common multiples exist).\<close>
\<comment> \<open>Lemma: g = \<gamma>*\<delta> (with a, a' \<in> A) lifts to a loop in the helix covering.
   This is the KEY property distinguishing f-lift (non-loop) from g-lift (loop).
   Combined with Theorem_54_3, this gives: if [f]^m = [g]^k then m = 0.\<close>
lemma helix_g_lift_is_loop:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B" and "a' \<in> A"
      and "top1_is_path_on U (subspace_topology X TX U) a a' gamma"
      and "top1_is_path_on V (subspace_topology X TX V) a' a delta"
  shows "\<exists>(E::('a \<times> int) set) TE (p0::('a \<times> int) \<Rightarrow> 'a) e0.
      top1_covering_map_on E TE X TX p0
    \<and> is_topology_on E TE
    \<and> e0 \<in> E \<and> p0 e0 = a
    \<and> (\<exists>gtilde. top1_is_path_on E TE e0 e0 gtilde
        \<and> (\<forall>s\<in>I_set. p0 (gtilde s) = top1_path_product gamma delta s))"
proof -
    \<comment> \<open>Use the same helix covering as in Theorem_63_1.\<close>
    have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
    have ha'_U: "a' \<in> U" using assms(5,11) by (by100 blast)
    have ha_V: "a \<in> V" using assms(5,9) by (by100 blast)
    have ha'_V: "a' \<in> V" using assms(5,11) by (by100 blast)
    have hU_open_TX: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
    have hV_open_TX: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
    have hA_open_TX: "A \<in> TX" using assms(7) unfolding openin_on_def by (by100 blast)
    have hB_open_TX: "B \<in> TX" using assms(8) unfolding openin_on_def by (by100 blast)
    have hAB_UV: "A \<union> B = U \<inter> V" using assms(5) by simp
    have hAB_disj: "A \<inter> B = {}" using assms(6) .
    \<comment> \<open>Same E, TE, p0 as 63.1.\<close>
    define E :: "('a \<times> int) set" where
      "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
    define TE :: "('a \<times> int) set set" where
      "TE = {W. W \<subseteq> E \<and>
        (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
        (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
    define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
    define e0 :: "'a \<times> int" where "e0 = (a, 0)"
    have he0_E: "e0 \<in> E" unfolding e0_def E_def using ha_U by simp
    have hp0e0: "p0 e0 = a" unfolding p0_def e0_def by simp
    have hcov_and_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
    proof -
      note h = helix_covering_construction[OF assms(1-8)]
      have "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
        unfolding E_def by auto
      moreover have "TE = {W. W \<subseteq> E \<and>
          (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
          (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
                {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
        unfolding TE_def E_def by auto
      moreover have "p0 = fst" unfolding p0_def by simp
      ultimately show ?thesis using h by simp
    qed
    hence hTE: "is_topology_on E TE" and hcov: "top1_covering_map_on E TE X TX p0"
      by auto
    \<comment> \<open>g-lift: \<gamma>_lift on [0,1/2], \<delta>_lift on [1/2,1].
       \<gamma>_lift(s) = (\<gamma>(s), 0). \<delta>_lift(s) = norm(\<delta>(s), -1).
       Since a' \<in> A: norm(a', -1) = (a', 0) = \<gamma>_lift(1). Junction OK.
       Since a \<in> A: norm(a, -1) = (a, 0) = e0. LOOP!\<close>
    define gtilde :: "real \<Rightarrow> ('a \<times> int)" where
      "gtilde = (\<lambda>s. if s \<le> 1/2
        then (gamma (2*s), 0)
        else (let y = delta (2*s - 1) in
              if y \<in> A then (y, 0)
              else if y \<in> B then (y, -2)
              else (y, -1)))"
    \<comment> \<open>Note: norm(y, -1) = (y, 0) if y \<in> A, (y, -2) if y \<in> B, (y, -1) if y \<in> V\U.\<close>
    have hgt_path: "top1_is_path_on E TE e0 e0 gtilde"
    proof -
      define \<gamma>_lift where "\<gamma>_lift = (\<lambda>s. (gamma s, 0::int))"
      define \<delta>_lift where "\<delta>_lift = (\<lambda>s. let y = delta s in
        if y \<in> A then (y, 0::int) else if y \<in> B then (y, -2::int) else (y, -1::int))"
      have hgt_eq: "gtilde = top1_path_product \<gamma>_lift \<delta>_lift"
        unfolding gtilde_def top1_path_product_def \<gamma>_lift_def \<delta>_lift_def by (rule ext) auto
      \<comment> \<open>\<gamma>_lift: path from (a,0) to (a',0) in E. Same as \<alpha>-lift but with \<gamma>.\<close>
      have h\<gamma>_lift: "top1_is_path_on E TE (a, 0) (a', 0) \<gamma>_lift"
      proof -
        have h\<gamma>_U: "top1_is_path_on U (subspace_topology X TX U) a a' gamma" by (rule assms(12))
        show ?thesis unfolding top1_is_path_on_def
        proof (intro conjI)
          show "top1_continuous_map_on I_set I_top E TE \<gamma>_lift"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set"
            hence "gamma s \<in> U" using h\<gamma>_U
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "\<gamma>_lift s \<in> E" unfolding \<gamma>_lift_def E_def by auto
          next
            fix W assume hW: "W \<in> TE"
            have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
            proof -
              have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
              hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
              thus ?thesis by simp
            qed
            have "{s \<in> I_set. \<gamma>_lift s \<in> W} = {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            proof (rule set_eqI, rule iffI)
              fix s assume "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}"
              thus "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
                using h\<gamma>_U unfolding top1_is_path_on_def top1_continuous_map_on_def \<gamma>_lift_def
                by auto
            next
              fix s assume "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
              thus "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}" unfolding \<gamma>_lift_def by simp
            qed
            moreover have "{s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
            proof -
              have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
                using hslice unfolding subspace_topology_def by (by100 blast)
              thus ?thesis using h\<gamma>_U unfolding top1_is_path_on_def top1_continuous_map_on_def
                by (by100 blast)
            qed
            ultimately show "{s \<in> I_set. \<gamma>_lift s \<in> W} \<in> I_top" by simp
          qed
          show "\<gamma>_lift 0 = (a, 0::int)" unfolding \<gamma>_lift_def
            using h\<gamma>_U unfolding top1_is_path_on_def by simp
          show "\<gamma>_lift 1 = (a', 0::int)" unfolding \<gamma>_lift_def
            using h\<gamma>_U unfolding top1_is_path_on_def by simp
        qed
      qed
      \<comment> \<open>\<delta>_lift: path from (a',0) to (a,0) in E. Uses odd-slice at level -1.\<close>
      have h\<delta>_lift: "top1_is_path_on E TE (a', 0) (a, 0) \<delta>_lift"
      proof -
        have h\<delta>_V: "top1_is_path_on V (subspace_topology X TX V) a' a delta" by (rule assms(13))
        show ?thesis unfolding top1_is_path_on_def
        proof (intro conjI)
          show "top1_continuous_map_on I_set I_top E TE \<delta>_lift"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s assume "s \<in> I_set"
            hence "delta s \<in> V" using h\<delta>_V
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "\<delta>_lift s \<in> E" unfolding \<delta>_lift_def E_def Let_def
              using hAB_UV hAB_disj by auto
          next
            fix W assume hW: "W \<in> TE"
            \<comment> \<open>Odd-slice at n = -1: {x\<in>A.(x,0)\<in>W} \<union> {x\<in>B.(x,-2)\<in>W} \<union> {x\<in>V\U.(x,-1)\<in>W}.\<close>
            have hV_slice: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                {x \<in> V - U. (x, -1::int) \<in> W} \<in> TX"
            proof -
              have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX"
                using hW unfolding TE_def by (by100 blast)
              hence "{x \<in> A. (x, 2*(-1::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(-1::int)) \<in> W} \<union>
                  {x \<in> V-U. (x, 2*(-1::int)+1) \<in> W} \<in> TX" by (rule spec)
              thus ?thesis by simp
            qed
            have heq: "{s \<in> I_set. \<delta>_lift s \<in> W} =
                {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                    {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
            proof (rule set_eqI, rule iffI)
              fix s assume hs: "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}"
              hence "s \<in> I_set" "\<delta>_lift s \<in> W" by auto
              have "delta s \<in> V" using \<open>s \<in> I_set\<close> h\<delta>_V
                unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
              hence "delta s \<in> A \<or> delta s \<in> B \<or> delta s \<in> V - U"
                using hAB_UV by (by100 blast)
              have "delta s \<in> {x \<in> A. (x, 0::int) \<in> W} \<union>
                  {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W}"
              proof -
                from \<open>delta s \<in> A \<or> delta s \<in> B \<or> delta s \<in> V - U\<close> show ?thesis
                proof (elim disjE)
                  assume "delta s \<in> A"
                  hence "\<delta>_lift s = (delta s, 0::int)" unfolding \<delta>_lift_def Let_def by simp
                  hence "(delta s, 0::int) \<in> W" using \<open>\<delta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>delta s \<in> A\<close> by (by100 blast)
                next
                  assume "delta s \<in> B"
                  hence "\<delta>_lift s = (delta s, -2::int)" unfolding \<delta>_lift_def Let_def
                    using hAB_disj by auto
                  hence "(delta s, -2::int) \<in> W" using \<open>\<delta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>delta s \<in> B\<close> by (by100 blast)
                next
                  assume "delta s \<in> V - U"
                  hence "delta s \<notin> A" "delta s \<notin> B" using hAB_UV by (by100 blast)+
                  hence "\<delta>_lift s = (delta s, -1::int)" unfolding \<delta>_lift_def Let_def by auto
                  hence "(delta s, -1::int) \<in> W" using \<open>\<delta>_lift s \<in> W\<close> by simp
                  thus ?thesis using \<open>delta s \<in> V - U\<close> by (by100 blast)
                qed
              qed
              thus "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                  {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
                using \<open>s \<in> I_set\<close> by (by100 blast)
            next
              fix s assume hs: "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                  {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
              hence "s \<in> I_set" by simp
              from hs have hcases: "delta s \<in> A \<and> (delta s, 0::int) \<in> W \<or>
                  delta s \<in> B \<and> (delta s, -2::int) \<in> W \<or>
                  delta s \<in> V - U \<and> (delta s, -1::int) \<in> W" by (by100 blast)
              have "\<delta>_lift s \<in> W"
              proof -
                from hcases show ?thesis
                proof (elim disjE conjE)
                  assume "delta s \<in> A" "(delta s, 0::int) \<in> W"
                  hence "\<delta>_lift s = (delta s, 0::int)" unfolding \<delta>_lift_def Let_def by simp
                  thus ?thesis using \<open>(delta s, 0) \<in> W\<close> by simp
                next
                  assume "delta s \<in> B" "(delta s, -2::int) \<in> W"
                  hence "\<delta>_lift s = (delta s, -2::int)" unfolding \<delta>_lift_def Let_def
                    using hAB_disj by auto
                  thus ?thesis using \<open>(delta s, -2) \<in> W\<close> by simp
                next
                  assume "delta s \<in> V - U" "(delta s, -1::int) \<in> W"
                  hence "delta s \<notin> A" "delta s \<notin> B" using hAB_UV by (by100 blast)+
                  hence "\<delta>_lift s = (delta s, -1::int)" unfolding \<delta>_lift_def Let_def by auto
                  thus ?thesis using \<open>(delta s, -1) \<in> W\<close> by simp
                qed
              qed
              thus "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}" using \<open>s \<in> I_set\<close> by (by100 blast)
            qed
            have hV_sub_open: "{x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W}
                \<in> subspace_topology X TX V"
            proof -
              have hsub: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                  {x \<in> V - U. (x, -1::int) \<in> W} \<subseteq> V" using hAB_UV by (by100 blast)
              thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
            qed
            have "{s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})} \<in> I_top"
              using h\<delta>_V hV_sub_open
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "{s \<in> I_set. \<delta>_lift s \<in> W} \<in> I_top" using heq by simp
          qed
          show "\<delta>_lift 0 = (a', 0::int)"
            unfolding \<delta>_lift_def Let_def using assms(13) assms(11) hAB_disj
            unfolding top1_is_path_on_def by auto
          show "\<delta>_lift 1 = (a, 0::int)"
            unfolding \<delta>_lift_def Let_def using assms(13) assms(9)
            unfolding top1_is_path_on_def by auto
        qed
      qed
      have hTX_E: "is_topology_on E TE" by (rule hTE)
      have "top1_is_path_on E TE (a, 0) (a, 0) (top1_path_product \<gamma>_lift \<delta>_lift)"
        by (rule top1_path_product_is_path[OF hTX_E h\<gamma>_lift h\<delta>_lift])
      thus ?thesis unfolding hgt_eq e0_def .
    qed
    have hgt_lift: "\<forall>s\<in>I_set. p0 (gtilde s) = top1_path_product gamma delta s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hs_range: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
      show "p0 (gtilde s) = top1_path_product gamma delta s"
      proof (cases "s \<le> 1/2")
        case True
        hence "gtilde s = (gamma (2*s), 0)" unfolding gtilde_def by simp
        thus ?thesis unfolding p0_def top1_path_product_def using True by simp
      next
        case False
        hence hs_half: "s > 1/2" by simp
        define y where "y = delta (2*s - 1)"
        have "gtilde s = (if y \<in> A then (y, 0) else if y \<in> B then (y, -2) else (y, -1))"
          unfolding gtilde_def y_def using hs_half by (simp add: Let_def)
        hence "p0 (gtilde s) = y" unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
        thus ?thesis unfolding y_def top1_path_product_def using False by simp
      qed
    qed
    show ?thesis
      using hcov hTE he0_E hp0e0 hgt_path hgt_lift
      by (intro exI[of _ E] exI[of _ TE] exI[of _ p0] exI[of _ e0]) (by100 blast)
  qed

text \<open>N-fold product of a loop: f^0 = const, f^(n+1) = f * f^n.\<close>
fun top1_path_power :: "(real \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_path_power f x 0 = top1_constant_path x"
| "top1_path_power f x (Suc n) = top1_path_product f (top1_path_power f x n)"

lemma top1_path_power_is_path:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_is_path_on X TX a a (top1_path_power f a n)"
proof (induction n)
  case 0
  have haX: "a \<in> X"
    using top1_is_loop_on_start[OF assms(2)]
          top1_is_loop_on_continuous[OF assms(2)]
    unfolding top1_continuous_map_on_def top1_unit_interval_def by force
  thus ?case by (simp add: top1_constant_path_is_path[OF assms(1)])
next
  case (Suc n)
  have hf: "top1_is_path_on X TX a a f"
    using assms(2) unfolding top1_is_loop_on_def by simp
  show ?case by (simp add: top1_path_product_is_path[OF assms(1) hf Suc])
qed

lemma top1_path_power_is_loop:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_is_loop_on X TX a (top1_path_power f a n)"
  using top1_path_power_is_path[OF assms] unfolding top1_is_loop_on_def by simp

text \<open>Helper: a path in a subspace U (with subspace topology from X) is also a path in X.\<close>
lemma path_in_subspace_is_path_in_space:
  assumes "is_topology_on X TX" and "U \<subseteq> X" and "openin_on X TX U"
  and "top1_is_path_on U (subspace_topology X TX U) a' b' f"
  shows "top1_is_path_on X TX a' b' f"
  unfolding top1_is_path_on_def top1_continuous_map_on_def
proof (intro conjI ballI)
  fix s assume hs: "s \<in> I_set"
  have "f s \<in> U" using assms(4) hs unfolding top1_is_path_on_def top1_continuous_map_on_def
    by (by100 blast)
  thus "f s \<in> X" using assms(2) by (by100 blast)
next
  fix W assume hW: "W \<in> TX"
  have hUW: "U \<inter> W \<in> subspace_topology X TX U"
    unfolding subspace_topology_def using hW by blast
  have h_pre: "{s \<in> I_set. f s \<in> U \<inter> W} \<in> I_top"
    using assms(4) hUW unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
  have h_in_U: "\<forall>s\<in>I_set. f s \<in> U"
    using assms(4) unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
  have "{s \<in> I_set. f s \<in> W} = {s \<in> I_set. f s \<in> U \<inter> W}"
    using h_in_U by (by100 blast)
  thus "{s \<in> I_set. f s \<in> W} \<in> I_top" using h_pre by simp
next
  show "f 0 = a'" using assms(4) unfolding top1_is_path_on_def by (by100 blast)
next
  show "f 1 = b'" using assms(4) unfolding top1_is_path_on_def by (by100 blast)
qed

\<comment> \<open>Theorem 63.1(c) — Main result: subgroups generated by [f] and [g] intersect trivially.
   Under the same hypotheses as Theorem_63_1_loop_nontrivial, with additional paths
   \<gamma>: a \<rightarrow> a' in U and \<delta>: a' \<rightarrow> a in V (where a' \<in> A), and g = \<gamma>*\<delta>:
   If the m-fold product f^m is path-homotopic to the k-fold product g^k in X, then m = 0.
   Proof sketch (Munkres Step 3+5):
     - f^m lifts from e_0 = (a,0) to (a, 2*m) in the helix covering (by concatenating shifted lifts).
     - g^k lifts to a loop at e_0 = (a,0) (since each g-lift is a loop, by helix_g_lift_is_loop).
     - By Theorem_54_3 (unique lift endpoints), if [f]^m = [g]^k then (a,2*m) = (a,0), so m = 0.\<close>

\<comment> \<open>Standalone f^m lift: in the helix covering, f^m lifts from (a,0) to (a,2m).
   Factored out for reuse by both 63.1(c) and 63.1(c)_reverse.\<close>
lemma helix_f_power_lift:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
      and "top1_covering_map_on E TE X TX p0"
      and "is_topology_on E TE"
      and "(a, 0::int) \<in> E"
      and "p0 (a, 0::int) = a"
      \<comment> \<open>TE slice conditions (needed for lift continuity proofs).\<close>
      and "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> U. (x, 2*n) \<in> W} \<in> TX"
      and "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX"
      \<comment> \<open>E membership for even/odd sheets.\<close>
      and "\<And>x n. x \<in> U \<Longrightarrow> (x, 2*n) \<in> E"
      and "\<And>x n. x \<in> V - U \<Longrightarrow> (x, 2*n + 1) \<in> E"
      and "\<And>x n. x \<in> A \<Longrightarrow> (x, 2*n + 2) \<in> E"
      and "\<And>x n. x \<in> B \<Longrightarrow> (x, 2*n) \<in> E"
      and "p0 = fst"
      \<comment> \<open>TE characterization: W \<in> TE iff W \<subseteq> E + slice conditions.\<close>
      \<comment> \<open>E characterization for T_E proof.\<close>
      and "\<And>x m. (x, m) \<in> E \<Longrightarrow> (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)"
      and "\<And>W. \<lbrakk>W \<subseteq> E; \<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX;
          \<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                    {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX\<rbrakk> \<Longrightarrow> W \<in> TE"
  shows "\<exists>ftm. top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm \<and>
      (\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s)"
proof -
  \<comment> \<open>Base f-lift: ftilde_0 from (a,0) to (a,2).\<close>
  define ftilde_0 :: "real \<Rightarrow> ('a \<times> int)" where
    "ftilde_0 = (\<lambda>s. if s \<le> 1/2 then (alpha (2*s), 0)
      else (let y = beta (2*s - 1) in
            if y \<in> A then (y, 2) else if y \<in> B then (y, 0) else (y, 1)))"
  define \<alpha>_lift where "\<alpha>_lift = (\<lambda>s. (alpha s, 0::int))"
  define \<beta>_lift where "\<beta>_lift = (\<lambda>s. let y = beta s in
    if y \<in> A then (y, 2::int) else if y \<in> B then (y, 0::int) else (y, 1::int))"
  have hft_eq: "ftilde_0 = top1_path_product \<alpha>_lift \<beta>_lift"
    unfolding ftilde_0_def top1_path_product_def \<alpha>_lift_def \<beta>_lift_def by (rule ext) auto
  have h\<alpha>_lift_path: "top1_is_path_on E TE (a, 0) (b, 0) \<alpha>_lift"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top E TE \<alpha>_lift"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      hence "alpha s \<in> U" using assms(11)
        unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      thus "\<alpha>_lift s \<in> E" unfolding \<alpha>_lift_def using assms(19)[of "alpha s" 0] by simp
    next
      fix W assume hW: "W \<in> TE"
      have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
        using assms(17)[OF hW, of 0] by simp
      have "{s \<in> I_set. \<alpha>_lift s \<in> W} = {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}"
        hence hs: "s \<in> I_set" and "\<alpha>_lift s \<in> W" by auto
        have "alpha s \<in> U" using assms(11) hs
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
          using hs \<open>\<alpha>_lift s \<in> W\<close> unfolding \<alpha>_lift_def by auto
      next
        fix s assume "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
        thus "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}" unfolding \<alpha>_lift_def by simp
      qed
      moreover have "{s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
      proof -
        have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
          unfolding subspace_topology_def using hslice by blast
        thus ?thesis using assms(11)
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      qed
      ultimately show "{s \<in> I_set. \<alpha>_lift s \<in> W} \<in> I_top" by simp
    qed
  next
    show "\<alpha>_lift 0 = (a, 0)" unfolding \<alpha>_lift_def
      using assms(11) unfolding top1_is_path_on_def by (by100 blast)
  next
    show "\<alpha>_lift 1 = (b, 0)" unfolding \<alpha>_lift_def
      using assms(11) unfolding top1_is_path_on_def by (by100 blast)
  qed
  have h\<beta>_lift_path: "top1_is_path_on E TE (b, 0) (a, 2) \<beta>_lift"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top E TE \<beta>_lift"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume hs: "s \<in> I_set"
      have "beta s \<in> V" using assms(12) hs
        unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      thus "\<beta>_lift s \<in> E"
      proof -
        have "beta s \<in> V" by (rule \<open>beta s \<in> V\<close>)
        show ?thesis
        proof (cases "beta s \<in> A")
          case True
          hence "\<beta>_lift s = (beta s, 2)" unfolding \<beta>_lift_def Let_def by simp
          moreover have "(beta s, 2) \<in> E" using assms(21)[of "beta s" 0] True by simp
          ultimately show ?thesis by simp
        next
          case False
          show ?thesis
          proof (cases "beta s \<in> B")
            case True
            hence "\<beta>_lift s = (beta s, 0)" unfolding \<beta>_lift_def Let_def using False by simp
            moreover have "(beta s, 0) \<in> E" using assms(22)[of "beta s" 0] True by simp
            ultimately show ?thesis by simp
          next
            case bFalse: False
            hence "beta s \<in> V - U" using \<open>beta s \<in> V\<close> assms(5) \<open>beta s \<notin> A\<close> by (by100 blast)
            hence "\<beta>_lift s = (beta s, 1)" unfolding \<beta>_lift_def Let_def using False bFalse by simp
            moreover have "(beta s, 1) \<in> E" using assms(20)[of "beta s" 0] \<open>beta s \<in> V - U\<close> by simp
            ultimately show ?thesis by simp
          qed
        qed
      qed
    next
      fix W assume hW: "W \<in> TE"
      have hV_slice: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
          {x \<in> V - U. (x, 1::int) \<in> W} \<in> TX"
        using assms(18)[OF hW, of 0] by simp
      have heq: "{s \<in> I_set. \<beta>_lift s \<in> W} =
          {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
              {x \<in> V - U. (x, 1::int) \<in> W})}"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}"
        hence hs: "s \<in> I_set" and hW': "\<beta>_lift s \<in> W" by auto
        have "beta s \<in> V" using assms(12) hs
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
            {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
          using hs hW' assms(5,6) unfolding \<beta>_lift_def Let_def by (auto split: if_splits)
      next
        fix s assume "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
            {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
        hence hs: "s \<in> I_set" and hds: "beta s \<in> {x \<in> A. (x, 2::int) \<in> W} \<union>
            {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W}" by auto
        have hAsub: "A \<subseteq> U" and hBsub: "B \<subseteq> U" using assms(5) by (by100 blast)+
        have "\<beta>_lift s \<in> W"
        proof -
          have "beta s \<in> A \<and> (beta s, 2) \<in> W \<or>
                beta s \<in> B \<and> (beta s, 0) \<in> W \<or>
                beta s \<in> V - U \<and> (beta s, 1) \<in> W" using hds by (by100 blast)
          thus ?thesis unfolding \<beta>_lift_def Let_def using assms(6) hAsub hBsub
            by (auto split: if_splits)
        qed
        thus "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}" using hs by (by100 blast)
      qed
      have hV_sub_open: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
          {x \<in> V - U. (x, 1::int) \<in> W} \<in> subspace_topology X TX V"
      proof -
        have "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
            {x \<in> V - U. (x, 1::int) \<in> W} \<subseteq> V"
          using assms(5) by (by100 blast)
        thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
      qed
      have "{s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
          {x \<in> V - U. (x, 1::int) \<in> W})} \<in> I_top"
        using assms(12) hV_sub_open
        unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      thus "{s \<in> I_set. \<beta>_lift s \<in> W} \<in> I_top" using heq by simp
    qed
  next
    show "\<beta>_lift 0 = (b, 0)" unfolding \<beta>_lift_def Let_def
      using assms(12) assms(10) assms(6) unfolding top1_is_path_on_def by auto
  next
    show "\<beta>_lift 1 = (a, 2)" unfolding \<beta>_lift_def Let_def
      using assms(12) assms(9) assms(6) unfolding top1_is_path_on_def by auto
  qed
  have hft0_path: "top1_is_path_on E TE (a, 0) (a, 2) ftilde_0"
    unfolding hft_eq by (rule top1_path_product_is_path[OF assms(14) h\<alpha>_lift_path h\<beta>_lift_path])
  have hft0_proj: "\<forall>s\<in>I_set. p0 (ftilde_0 s) = top1_path_product alpha beta s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "p0 (ftilde_0 s) = top1_path_product alpha beta s"
    proof (cases "s \<le> 1/2")
      case True thus ?thesis unfolding ftilde_0_def assms(23) top1_path_product_def by simp
    next
      case False
      define y where "y = beta (2*s - 1)"
      have "ftilde_0 s = (if y \<in> A then (y, 2) else if y \<in> B then (y, 0) else (y, 1))"
        unfolding ftilde_0_def y_def using False by (simp add: Let_def)
      hence "p0 (ftilde_0 s) = y" unfolding assms(23) by (cases "y \<in> A"; cases "y \<in> B"; simp)
      thus ?thesis unfolding y_def top1_path_product_def using False by simp
    qed
  qed
  \<comment> \<open>Deck transformation T and induction — same as Theorem_63_1_c.\<close>
  define T :: "'a \<times> int \<Rightarrow> 'a \<times> int" where "T = (\<lambda>(x,m). (x, m + 2))"
  have hT_E: "\<And>e. e \<in> E \<Longrightarrow> T e \<in> E"
  proof -
    fix e assume he: "e \<in> E"
    obtain x n where hxn: "e = (x, n)" by (cases e) auto
    have "(even n \<and> x \<in> U) \<or> (odd n \<and> x \<in> V - U)"
      using assms(24)[of x n] he hxn by simp
    thus "T e \<in> E"
    proof
      assume "even n \<and> x \<in> U"
      hence "x \<in> U" "even (n + 2)" by auto
      thus ?thesis using assms(19)[of x "(n+2) div 2"] hxn unfolding T_def by simp
    next
      assume "odd n \<and> x \<in> V - U"
      hence "x \<in> V - U" "odd (n + 2)" by auto
      thus ?thesis using assms(20)[of x "(n + 2 - 1) div 2"] hxn unfolding T_def
        by (simp add: algebra_simps)
    qed
  qed
  have hT_p0: "\<And>e. p0 (T e) = p0 e" unfolding T_def assms(23) by auto
  have hT_cont: "top1_continuous_map_on E TE E TE T"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix e assume "e \<in> E" thus "T e \<in> E" using hT_E by simp
  next
    fix W assume hW: "W \<in> TE"
    show "{e \<in> E. T e \<in> W} \<in> TE"
    proof (rule assms(25))
      show "{e \<in> E. T e \<in> W} \<subseteq> E" by (by100 blast)
    next
      show "\<forall>n::int. {x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} \<in> TX"
      proof
        fix n :: int
        have "{x \<in> U. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} = {x \<in> U. (x, 2*(n+1)) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> U. (x, 2*n) \<in> {e \<in> E. T e \<in> W}}"
          hence "x \<in> U" "T (x, 2*n) \<in> W" by auto
          thus "x \<in> {x \<in> U. (x, 2*(n+1)) \<in> W}" unfolding T_def by (simp add: algebra_simps)
        next
          fix x assume "x \<in> {x \<in> U. (x, 2*(n+1)) \<in> W}"
          hence "x \<in> U" "(x, 2*n + 2) \<in> W" by (auto simp: algebra_simps)
          moreover have "(x, 2*n) \<in> E" using \<open>x \<in> U\<close> assms(19) by simp
          moreover have "T (x, 2*n) = (x, 2*n + 2)" unfolding T_def by simp
          ultimately show "x \<in> {x \<in> U. (x, 2*n) \<in> {e \<in> E. T e \<in> W}}" by auto
        qed
        also have "... \<in> TX" using assms(17)[OF hW, of "n+1"] by (simp add: algebra_simps)
        finally show "{x \<in> U. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} \<in> TX" .
      qed
    next
      show "\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> V - U. (x, 2*n + 1) \<in> {e \<in> E. T e \<in> W}} \<in> TX"
      proof
        fix n :: int
        have h_A: "{x \<in> A. (x, 2*n + 2) \<in> {e \<in> E. T e \<in> W}} = {x \<in> A. (x, 2*(n+1) + 2) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> A. (x, 2*n + 2) \<in> {e \<in> E. T e \<in> W}}"
          thus "x \<in> {x \<in> A. (x, 2*(n+1) + 2) \<in> W}" unfolding T_def by (simp add: algebra_simps)
        next
          fix x assume "x \<in> {x \<in> A. (x, 2*(n+1) + 2) \<in> W}"
          hence "x \<in> A" "(x, 2*n + 4) \<in> W" by (auto simp: algebra_simps)
          moreover have "(x, 2*n+2) \<in> E" using \<open>x \<in> A\<close> assms(21) by simp
          moreover have "T (x, 2*n+2) = (x, 2*n+4)" unfolding T_def by simp
          ultimately show "x \<in> {x \<in> A. (x, 2*n+2) \<in> {e \<in> E. T e \<in> W}}" by auto
        qed
        have h_B: "{x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} = {x \<in> B. (x, 2*(n+1)) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}}"
          thus "x \<in> {x \<in> B. (x, 2*(n+1)) \<in> W}" unfolding T_def by (simp add: algebra_simps)
        next
          fix x assume "x \<in> {x \<in> B. (x, 2*(n+1)) \<in> W}"
          hence "x \<in> B" "(x, 2*n+2) \<in> W" by (auto simp: algebra_simps)
          moreover have "(x, 2*n) \<in> E" using \<open>x \<in> B\<close> assms(22) by simp
          moreover have "T (x, 2*n) = (x, 2*n+2)" unfolding T_def by simp
          ultimately show "x \<in> {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}}" by auto
        qed
        have h_VU: "{x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}} = {x \<in> V-U. (x, 2*(n+1)+1) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}}"
          thus "x \<in> {x \<in> V-U. (x, 2*(n+1)+1) \<in> W}" unfolding T_def by (simp add: algebra_simps)
        next
          fix x assume "x \<in> {x \<in> V-U. (x, 2*(n+1)+1) \<in> W}"
          hence "x \<in> V-U" "(x, 2*n+3) \<in> W" by (auto simp: algebra_simps)
          moreover have "(x, 2*n+1) \<in> E" using \<open>x \<in> V-U\<close> assms(20) by simp
          moreover have "T (x, 2*n+1) = (x, 2*n+3)" unfolding T_def by simp
          ultimately show "x \<in> {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}}" by auto
        qed
        have "{x \<in> A. (x, 2*n+2) \<in> {e \<in> E. T e \<in> W}} \<union>
            {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}}
          = {x \<in> A. (x, 2*(n+1)+2) \<in> W} \<union> {x \<in> B. (x, 2*(n+1)) \<in> W} \<union>
            {x \<in> V-U. (x, 2*(n+1)+1) \<in> W}"
          using h_A h_B h_VU by simp
        also have "... \<in> TX" using assms(18)[OF hW, of "n+1"] by (simp add: algebra_simps)
        finally show "{x \<in> A. (x, 2*n+2) \<in> {e \<in> E. T e \<in> W}} \<union>
            {x \<in> B. (x, 2*n) \<in> {e \<in> E. T e \<in> W}} \<union>
            {x \<in> V-U. (x, 2*n+1) \<in> {e \<in> E. T e \<in> W}} \<in> TX" .
      qed
    qed
  qed
  \<comment> \<open>Induction: f^m lift from (a,0) to (a,2m).\<close>
  show ?thesis
  proof (induction m)
    case 0
    have "top1_is_path_on E TE (a, 0) (a, 0) (top1_constant_path (a, 0))"
      by (rule top1_constant_path_is_path[OF assms(14,15)])
    moreover have "\<forall>s\<in>I_set. p0 (top1_constant_path (a, 0) s) =
        top1_path_power (top1_path_product alpha beta) a 0 s"
      by (simp add: top1_constant_path_def assms(16))
    ultimately show ?case by (intro exI[of _ "top1_constant_path (a, 0)"]) auto
  next
    case (Suc m)
    obtain ftm where hftm: "top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm"
        and hftm_proj: "\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s"
      using Suc by (by100 blast)
    define Tftm where "Tftm = T \<circ> ftm"
    have hTftm_path: "top1_is_path_on E TE (a, 2) (a, 2 * int m + 2) Tftm"
      unfolding top1_is_path_on_def top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume hs: "s \<in> I_set"
      have "ftm s \<in> E" using hftm hs unfolding top1_is_path_on_def top1_continuous_map_on_def
        by (by100 blast)
      thus "Tftm s \<in> E" unfolding Tftm_def comp_def using hT_E by (by100 blast)
    next
      fix W assume hW: "W \<in> TE"
      have hTinvW: "{e \<in> E. T e \<in> W} \<in> TE"
        using hT_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
      have "{s \<in> I_set. Tftm s \<in> W} = {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> I_set. Tftm s \<in> W}"
        hence hs: "s \<in> I_set" and "Tftm s \<in> W" by auto
        have "ftm s \<in> E" using hftm hs unfolding top1_is_path_on_def top1_continuous_map_on_def
          by (by100 blast)
        moreover have "T (ftm s) \<in> W" using \<open>Tftm s \<in> W\<close> unfolding Tftm_def comp_def by simp
        ultimately show "s \<in> {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}" using hs by (by100 blast)
      next
        fix s assume "s \<in> {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}"
        thus "s \<in> {s \<in> I_set. Tftm s \<in> W}" unfolding Tftm_def comp_def by (by100 blast)
      qed
      moreover have "{s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}} \<in> I_top"
        using hftm hTinvW unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      ultimately show "{s \<in> I_set. Tftm s \<in> W} \<in> I_top" by simp
    next
      show "Tftm 0 = (a, 2)"
      proof -
        have "ftm 0 = (a, 0)" using hftm unfolding top1_is_path_on_def by (by100 blast)
        thus ?thesis unfolding Tftm_def comp_def T_def by simp
      qed
    next
      show "Tftm 1 = (a, 2 * int m + 2)"
      proof -
        have "ftm 1 = (a, 2 * int m)" using hftm unfolding top1_is_path_on_def by (by100 blast)
        thus ?thesis unfolding Tftm_def comp_def T_def by simp
      qed
    qed
    have hTftm_proj: "\<forall>s\<in>I_set. p0 (Tftm s) = top1_path_power (top1_path_product alpha beta) a m s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "p0 (Tftm s) = p0 (T (ftm s))" unfolding Tftm_def comp_def by simp
      also have "... = p0 (ftm s)" using hT_p0 by simp
      also have "... = top1_path_power (top1_path_product alpha beta) a m s"
        using hftm_proj hs by (by100 blast)
      finally show "p0 (Tftm s) = top1_path_power (top1_path_product alpha beta) a m s" .
    qed
    define ftSm where "ftSm = top1_path_product ftilde_0 Tftm"
    have hftSm_path: "top1_is_path_on E TE (a, 0) (a, 2 * int m + 2) ftSm"
      unfolding ftSm_def by (rule top1_path_product_is_path[OF assms(14) hft0_path hTftm_path])
    have hftSm_end: "top1_is_path_on E TE (a, 0) (a, 2 * int (Suc m)) ftSm"
      using hftSm_path by (simp add: algebra_simps)
    have hftSm_proj: "\<forall>s\<in>I_set. p0 (ftSm s) = top1_path_power (top1_path_product alpha beta) a (Suc m) s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (ftSm s) = top1_path_power (top1_path_product alpha beta) a (Suc m) s"
      proof (cases "s \<le> 1/2")
        case True
        have "ftSm s = ftilde_0 (2*s)" unfolding ftSm_def top1_path_product_def using True by simp
        have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        hence "p0 (ftilde_0 (2*s)) = top1_path_product alpha beta (2*s)"
          using hft0_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
            = (top1_path_product alpha beta) (2*s)"
        proof -
          have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
              = top1_path_product (top1_path_product alpha beta)
                  (top1_path_power (top1_path_product alpha beta) a m) s" by simp
          also have "... = (top1_path_product alpha beta) (2*s)"
            unfolding top1_path_product_def using True by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>ftSm s = ftilde_0 (2*s)\<close> by simp
      next
        case False
        have "ftSm s = Tftm (2*s - 1)" unfolding ftSm_def top1_path_product_def using False by simp
        have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        hence "p0 (Tftm (2*s - 1)) = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
          using hTftm_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
            = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
        proof -
          have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
              = top1_path_product (top1_path_product alpha beta)
                  (top1_path_power (top1_path_product alpha beta) a m) s" by simp
          also have "... = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
            unfolding top1_path_product_def using False by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>ftSm s = Tftm (2*s - 1)\<close> by simp
      qed
    qed
    show ?case by (intro exI[of _ ftSm]) (use hftSm_end hftSm_proj in blast)
  qed
qed

lemma Theorem_63_1_c_subgroups_trivial:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
      \<comment> \<open>Additional 63.1(c) data: a' \<in> A, paths \<gamma> and \<delta>.\<close>
      and "a' \<in> A"
      and "top1_is_path_on U (subspace_topology X TX U) a a' gamma"
      and "top1_is_path_on V (subspace_topology X TX V) a' a delta"
      \<comment> \<open>Homotopy between f^m and g^k.\<close>
      and "top1_path_homotopic_on X TX a a
            (top1_path_power (top1_path_product alpha beta) a m)
            (top1_path_power (top1_path_product gamma delta) a k)"
  shows "m = 0"
proof (rule ccontr)
  assume "m \<noteq> 0" hence hm: "m > 0" by simp
  \<comment> \<open>Step 1: Construct helix covering (same as Theorem_63_1).\<close>
  have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
  have hb_U: "b \<in> U" using assms(5,10) by (by100 blast)
  have ha_V: "a \<in> V" using assms(5,9) by (by100 blast)
  have hb_V: "b \<in> V" using assms(5,10) by (by100 blast)
  have ha'_U: "a' \<in> U" using assms(5,13) by (by100 blast)
  have ha'_V: "a' \<in> V" using assms(5,13) by (by100 blast)
  have hU_open_TX: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
  have hV_open_TX: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
  have hA_open_TX: "A \<in> TX" using assms(7) unfolding openin_on_def by (by100 blast)
  have hB_open_TX: "B \<in> TX" using assms(8) unfolding openin_on_def by (by100 blast)
  define E :: "('a \<times> int) set" where
    "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
  define TE :: "('a \<times> int) set set" where
    "TE = {W. W \<subseteq> E \<and>
      (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
      (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
  define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
  define e0 :: "'a \<times> int" where "e0 = (a, 0)"
  have he0_E: "e0 \<in> E" unfolding e0_def E_def using ha_U by simp
  have hp0e0: "p0 e0 = a" unfolding p0_def e0_def by simp
  have hcov_and_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
  proof -
    note h = helix_covering_construction[OF assms(1-8)]
    have "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
      unfolding E_def by auto
    moreover have "TE = {W. W \<subseteq> E \<and>
        (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
        (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
              {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
      unfolding TE_def E_def by auto
    moreover have "p0 = fst" unfolding p0_def by simp
    ultimately show ?thesis using h by simp
  qed
  hence hTE: "is_topology_on E TE" and hcov: "top1_covering_map_on E TE X TX p0"
    by auto
  \<comment> \<open>Step 2: f^m lifts from e0 = (a,0) to (a, 2*(int m)) in E.\<close>
  \<comment> \<open>First construct the base f-lift (sheet 0): from (a,0) to (a,2).\<close>
  define ftilde_0 :: "real \<Rightarrow> ('a \<times> int)" where
    "ftilde_0 = (\<lambda>s. if s \<le> 1/2
      then (alpha (2*s), 0)
      else (let y = beta (2*s - 1) in
            if y \<in> A then (y, 2)
            else if y \<in> B then (y, 0)
            else (y, 1)))"
  have hft0_path: "top1_is_path_on E TE e0 (a, 2) ftilde_0"
  proof -
    define \<alpha>_lift where "\<alpha>_lift = (\<lambda>s. (alpha s, 0::int))"
    define \<beta>_lift where "\<beta>_lift = (\<lambda>s. let y = beta s in
      if y \<in> A then (y, 2::int) else if y \<in> B then (y, 0::int) else (y, 1::int))"
    have hft_eq: "ftilde_0 = top1_path_product \<alpha>_lift \<beta>_lift"
      unfolding ftilde_0_def top1_path_product_def \<alpha>_lift_def \<beta>_lift_def by (rule ext) auto
    have h\<alpha>_lift_path: "top1_is_path_on E TE (a, 0) (b, 0) \<alpha>_lift"
      unfolding top1_is_path_on_def
    proof (intro conjI)
      show "top1_continuous_map_on I_set I_top E TE \<alpha>_lift"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume "s \<in> I_set"
        hence "alpha s \<in> U" using assms(11)
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "\<alpha>_lift s \<in> E" unfolding \<alpha>_lift_def E_def by auto
      next
        fix W assume hW: "W \<in> TE"
        have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
        proof -
          have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
          hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
          thus ?thesis by simp
        qed
        have "{s \<in> I_set. \<alpha>_lift s \<in> W} = {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
        proof (rule set_eqI, rule iffI)
          fix s assume "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}"
          hence hs: "s \<in> I_set" and hW': "\<alpha>_lift s \<in> W" by auto
          have "alpha s \<in> U" using assms(11) hs
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            using hs hW' unfolding \<alpha>_lift_def by auto
        next
          fix s assume "s \<in> {s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
          thus "s \<in> {s \<in> I_set. \<alpha>_lift s \<in> W}" unfolding \<alpha>_lift_def by simp
        qed
        moreover have "{s \<in> I_set. alpha s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
        proof -
          have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
            unfolding subspace_topology_def using hslice by blast
          thus ?thesis using assms(11)
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        qed
        ultimately show "{s \<in> I_set. \<alpha>_lift s \<in> W} \<in> I_top" by simp
      qed
    next
      show "\<alpha>_lift 0 = (a, 0)" unfolding \<alpha>_lift_def
        using assms(11) unfolding top1_is_path_on_def by (by100 blast)
    next
      show "\<alpha>_lift 1 = (b, 0)" unfolding \<alpha>_lift_def
        using assms(11) unfolding top1_is_path_on_def by (by100 blast)
    qed
    have h\<beta>_lift_path: "top1_is_path_on E TE (b, 0) (a, 2) \<beta>_lift"
      unfolding top1_is_path_on_def
    proof (intro conjI)
      show "top1_continuous_map_on I_set I_top E TE \<beta>_lift"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume hs: "s \<in> I_set"
        have "beta s \<in> V" using assms(12) hs
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "\<beta>_lift s \<in> E" unfolding \<beta>_lift_def E_def Let_def
          using assms(5) by auto
      next
        fix W assume hW: "W \<in> TE"
        \<comment> \<open>V-slice at sheet 0: {x \<in> A. (x,2) \<in> W} \<union> {x \<in> B. (x,0) \<in> W} \<union> {x \<in> V-U. (x,1) \<in> W} \<in> TX.\<close>
        have hV_slice: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
            {x \<in> V - U. (x, 1::int) \<in> W} \<in> TX"
        proof -
          have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
              {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
          hence "{x \<in> A. (x, 2*(0::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(0::int)) \<in> W} \<union>
              {x \<in> V-U. (x, 2*(0::int)+1) \<in> W} \<in> TX" by (rule spec)
          thus ?thesis by simp
        qed
        \<comment> \<open>The preimage: \<beta>_lift(s) \<in> W iff beta(s) \<in> V-slice.\<close>
        have heq: "{s \<in> I_set. \<beta>_lift s \<in> W} =
            {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
                {x \<in> V - U. (x, 1::int) \<in> W})}"
        proof (rule set_eqI, rule iffI)
          fix s assume "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}"
          hence hs: "s \<in> I_set" and hW': "\<beta>_lift s \<in> W" by auto
          have "beta s \<in> V" using assms(12) hs
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          have "beta s \<in> A \<union> B \<or> beta s \<in> V - U" using \<open>beta s \<in> V\<close> assms(5) by (by100 blast)
          thus "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
              {x \<in> V - U. (x, 1::int) \<in> W})}"
            using hs hW' assms(6) unfolding \<beta>_lift_def Let_def by (auto split: if_splits)
        next
          fix s assume "s \<in> {s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union>
              {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W})}"
          hence hs: "s \<in> I_set" and hbs: "beta s \<in> {x \<in> A. (x, 2::int) \<in> W} \<union>
              {x \<in> B. (x, 0::int) \<in> W} \<union> {x \<in> V - U. (x, 1::int) \<in> W}" by auto
          have "\<beta>_lift s \<in> W"
          proof -
            have hAsub: "A \<subseteq> U" and hBsub: "B \<subseteq> U" using assms(5) by (by100 blast)+
            have "beta s \<in> A \<and> (beta s, 2) \<in> W \<or>
                  beta s \<in> B \<and> (beta s, 0) \<in> W \<or>
                  beta s \<in> V - U \<and> (beta s, 1) \<in> W" using hbs by (by100 blast)
            thus ?thesis unfolding \<beta>_lift_def Let_def using assms(6) hAsub hBsub
              by (auto split: if_splits)
          qed
          thus "s \<in> {s \<in> I_set. \<beta>_lift s \<in> W}" using hs by (by100 blast)
        qed
        \<comment> \<open>The V-slice is open in TX, hence in subspace topology of V.\<close>
        have hV_sub_open: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
            {x \<in> V - U. (x, 1::int) \<in> W} \<in> subspace_topology X TX V"
        proof -
          have hsub: "{x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
              {x \<in> V - U. (x, 1::int) \<in> W} \<subseteq> V"
            using assms(5) by (by100 blast)
          thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
        qed
        have "{s \<in> I_set. beta s \<in> ({x \<in> A. (x, 2::int) \<in> W} \<union> {x \<in> B. (x, 0::int) \<in> W} \<union>
            {x \<in> V - U. (x, 1::int) \<in> W})} \<in> I_top"
          using assms(12) hV_sub_open
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus "{s \<in> I_set. \<beta>_lift s \<in> W} \<in> I_top" using heq by simp
      qed
    next
      show "\<beta>_lift 0 = (b, 0)" unfolding \<beta>_lift_def Let_def
        using assms(12) assms(10) assms(6) unfolding top1_is_path_on_def by auto
    next
      show "\<beta>_lift 1 = (a, 2)" unfolding \<beta>_lift_def Let_def
        using assms(12) assms(9) assms(6) unfolding top1_is_path_on_def by auto
    qed
    show ?thesis unfolding hft_eq e0_def
      by (rule top1_path_product_is_path[OF hTE h\<alpha>_lift_path h\<beta>_lift_path])
  qed
  have hft0_proj: "\<forall>s\<in>I_set. p0 (ftilde_0 s) = top1_path_product alpha beta s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "p0 (ftilde_0 s) = top1_path_product alpha beta s"
    proof (cases "s \<le> 1/2")
      case True
      thus ?thesis unfolding ftilde_0_def p0_def top1_path_product_def by simp
    next
      case False
      define y where "y = beta (2*s - 1)"
      have "ftilde_0 s = (if y \<in> A then (y, 2) else if y \<in> B then (y, 0) else (y, 1))"
        unfolding ftilde_0_def y_def using False by (simp add: Let_def)
      hence "p0 (ftilde_0 s) = y"
        unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
      thus ?thesis unfolding y_def top1_path_product_def using False by simp
    qed
  qed
  \<comment> \<open>Deck transformation: T(x,m) = (x, m+2). Shifts sheets by 1.\<close>
  define T :: "'a \<times> int \<Rightarrow> 'a \<times> int" where "T = (\<lambda>(x,m). (x, m + 2))"
  have hT_E: "\<And>e. e \<in> E \<Longrightarrow> T e \<in> E" unfolding T_def E_def by auto
  have hT_p0: "\<And>e. p0 (T e) = p0 e" unfolding T_def p0_def by auto
  have hT_cont: "top1_continuous_map_on E TE E TE T"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix e assume "e \<in> E" thus "T e \<in> E" using hT_E by simp
  next
    fix W assume hW: "W \<in> TE"
    \<comment> \<open>T^{-1}(W) = {e \<in> E. T e \<in> W}. Show this is in TE.\<close>
    show "{e \<in> E. T e \<in> W} \<in> TE"
      unfolding TE_def
    proof (intro CollectI conjI allI)
      show "{e \<in> E. T e \<in> W} \<subseteq> E" by (by100 blast)
    next
      \<comment> \<open>Even slices: {x \<in> U. (x, 2n) \<in> T^{-1}(W)} = {x \<in> U. (x, 2n+2) \<in> W} = even slice n+1 of W.\<close>
      fix n :: int
      have "{x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} = {x \<in> U. (x, 2 * (n + 1)) \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}}"
        hence "x \<in> U" "T (x, 2*n) \<in> W" by auto
        hence "(x, 2*n + 2) \<in> W" unfolding T_def by simp
        thus "x \<in> {x \<in> U. (x, 2 * (n + 1)) \<in> W}" using \<open>x \<in> U\<close> by (simp add: algebra_simps)
      next
        fix x assume "x \<in> {x \<in> U. (x, 2 * (n + 1)) \<in> W}"
        hence "x \<in> U" "(x, 2*n + 2) \<in> W" by (auto simp: algebra_simps)
        have "(x, 2*n) \<in> E" unfolding E_def using \<open>x \<in> U\<close> by auto
        moreover have "T (x, 2*n) = (x, 2*n + 2)" unfolding T_def by simp
        ultimately show "x \<in> {x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}}"
          using \<open>x \<in> U\<close> \<open>(x, 2*n + 2) \<in> W\<close> by auto
      qed
      also have "... \<in> TX" using hW unfolding TE_def by (by100 blast)
      finally show "{x \<in> U. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} \<in> TX" .
    next
      \<comment> \<open>Odd slices: shift by +2, getting odd slice n+1 of W.\<close>
      fix n :: int
      have h_A: "{x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}} = {x \<in> A. (x, 2 * (n+1) + 2) \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}}"
        hence "x \<in> A" "T (x, 2*n + 2) \<in> W" by auto
        thus "x \<in> {x \<in> A. (x, 2 * (n+1) + 2) \<in> W}" unfolding T_def by (simp add: algebra_simps)
      next
        fix x assume "x \<in> {x \<in> A. (x, 2 * (n+1) + 2) \<in> W}"
        hence "x \<in> A" "(x, 2*n + 4) \<in> W" by (auto simp: algebra_simps)
        have "x \<in> U" using \<open>x \<in> A\<close> assms(5) by (by100 blast)
        have "(x, 2*n+2) \<in> E" unfolding E_def using \<open>x \<in> U\<close> by auto
        moreover have "T (x, 2*n+2) = (x, 2*n+4)" unfolding T_def by simp
        ultimately show "x \<in> {x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}}"
          using \<open>x \<in> A\<close> \<open>(x, 2*n+4) \<in> W\<close> by auto
      qed
      have h_B: "{x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} = {x \<in> B. (x, 2 * (n+1)) \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}}"
        hence "x \<in> B" "T (x, 2*n) \<in> W" by auto
        thus "x \<in> {x \<in> B. (x, 2 * (n+1)) \<in> W}" unfolding T_def by (simp add: algebra_simps)
      next
        fix x assume "x \<in> {x \<in> B. (x, 2 * (n+1)) \<in> W}"
        hence "x \<in> B" "(x, 2*n + 2) \<in> W" by (auto simp: algebra_simps)
        have "x \<in> U" using \<open>x \<in> B\<close> assms(5) by (by100 blast)
        have "(x, 2*n) \<in> E" unfolding E_def using \<open>x \<in> U\<close> by auto
        moreover have "T (x, 2*n) = (x, 2*n+2)" unfolding T_def by simp
        ultimately show "x \<in> {x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}}"
          using \<open>x \<in> B\<close> \<open>(x, 2*n+2) \<in> W\<close> by auto
      qed
      have h_VU: "{x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}} = {x \<in> V - U. (x, 2 * (n+1) + 1) \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}}"
        hence "x \<in> V - U" "T (x, 2*n+1) \<in> W" by auto
        thus "x \<in> {x \<in> V - U. (x, 2 * (n+1) + 1) \<in> W}" unfolding T_def by (simp add: algebra_simps)
      next
        fix x assume "x \<in> {x \<in> V - U. (x, 2 * (n+1) + 1) \<in> W}"
        hence "x \<in> V - U" "(x, 2*n + 3) \<in> W" by (auto simp: algebra_simps)
        have "(x, 2*n+1) \<in> E" unfolding E_def using \<open>x \<in> V - U\<close> by auto
        moreover have "T (x, 2*n+1) = (x, 2*n+3)" unfolding T_def by simp
        ultimately show "x \<in> {x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}}"
          using \<open>x \<in> V - U\<close> \<open>(x, 2*n+3) \<in> W\<close> by auto
      qed
      have "{x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}}
        = {x \<in> A. (x, 2*(n+1)+2) \<in> W} \<union> {x \<in> B. (x, 2*(n+1)) \<in> W} \<union>
          {x \<in> V - U. (x, 2*(n+1)+1) \<in> W}"
        using h_A h_B h_VU by simp
      also have "... \<in> TX" using hW unfolding TE_def by (by100 blast)
      finally show "{x \<in> A. (x, 2 * n + 2) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> B. (x, 2 * n) \<in> {e \<in> E. T e \<in> W}} \<union>
          {x \<in> V - U. (x, 2 * n + 1) \<in> {e \<in> E. T e \<in> W}} \<in> TX" .
    qed
  qed
  \<comment> \<open>T^n maps e0=(a,0) to (a, 2*int n).\<close>
  have hT_iter: "\<And>n::nat. (T ^^ n) e0 = (a, 2 * int n)"
  proof -
    fix n :: nat show "(T ^^ n) e0 = (a, 2 * int n)"
    proof (induction n)
      case 0 thus ?case unfolding e0_def by simp
    next
      case (Suc n) thus ?case unfolding T_def by simp
    qed
  qed
  \<comment> \<open>By induction: f^m lifts from e0 to (a, 2*int m).\<close>
  have hfm_lift: "\<exists>ftilde_m. top1_is_path_on E TE e0 (a, 2 * int m) ftilde_m \<and>
      (\<forall>s\<in>I_set. p0 (ftilde_m s) = top1_path_power (top1_path_product alpha beta) a m s)"
  proof (induction m)
    case 0
    have "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
      by (rule top1_constant_path_is_path[OF hTE he0_E])
    moreover have "e0 = (a, 2 * int 0)" unfolding e0_def by simp
    moreover have "\<forall>s\<in>I_set. p0 (top1_constant_path e0 s) = top1_path_power (top1_path_product alpha beta) a 0 s"
    proof
      fix s assume "s \<in> I_set"
      have lhs: "p0 (top1_constant_path e0 s) = a"
        unfolding top1_constant_path_def using hp0e0 by simp
      have rhs: "top1_path_power (top1_path_product alpha beta) a 0 s = a"
        by (simp add: top1_constant_path_def)
      show "p0 (top1_constant_path e0 s) = top1_path_power (top1_path_product alpha beta) a 0 s"
        using lhs rhs by simp
    qed
    ultimately show ?case by (intro exI[of _ "top1_constant_path e0"]) auto
  next
    case (Suc m)
    obtain ftm where hftm: "top1_is_path_on E TE e0 (a, 2 * int m) ftm"
        and hftm_proj: "\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s"
      using Suc by (by100 blast)
    \<comment> \<open>T \<circ> ftm: path from T(e0)=(a,2) to T((a,2m))=(a,2m+2), projects to f^m.\<close>
    define Tftm where "Tftm = T \<circ> ftm"
    have hTftm_path: "top1_is_path_on E TE (a, 2) (a, 2 * int m + 2) Tftm"
      unfolding top1_is_path_on_def top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume hs: "s \<in> I_set"
      have "ftm s \<in> E" using hftm hs unfolding top1_is_path_on_def top1_continuous_map_on_def
        by (by100 blast)
      thus "Tftm s \<in> E" unfolding Tftm_def comp_def using hT_E by (by100 blast)
    next
      fix W assume hW: "W \<in> TE"
      have hTinvW: "{e \<in> E. T e \<in> W} \<in> TE"
        using hT_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
      have "{s \<in> I_set. Tftm s \<in> W} = {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}"
      proof (rule set_eqI, rule iffI)
        fix s assume "s \<in> {s \<in> I_set. Tftm s \<in> W}"
        hence hs: "s \<in> I_set" and hTW: "Tftm s \<in> W" by auto
        have "ftm s \<in> E" using hftm hs unfolding top1_is_path_on_def top1_continuous_map_on_def
          by (by100 blast)
        moreover have "T (ftm s) \<in> W" using hTW unfolding Tftm_def comp_def by simp
        ultimately show "s \<in> {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}" using hs by (by100 blast)
      next
        fix s assume "s \<in> {s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}}"
        thus "s \<in> {s \<in> I_set. Tftm s \<in> W}" unfolding Tftm_def comp_def by (by100 blast)
      qed
      moreover have "{s \<in> I_set. ftm s \<in> {e \<in> E. T e \<in> W}} \<in> I_top"
        using hftm hTinvW unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      ultimately show "{s \<in> I_set. Tftm s \<in> W} \<in> I_top" by simp
    next
      show "Tftm 0 = (a, 2)"
      proof -
        have "ftm 0 = e0" using hftm unfolding top1_is_path_on_def by (by100 blast)
        thus ?thesis unfolding Tftm_def comp_def T_def e0_def by simp
      qed
    next
      show "Tftm 1 = (a, 2 * int m + 2)"
      proof -
        have "ftm 1 = (a, 2 * int m)" using hftm unfolding top1_is_path_on_def by (by100 blast)
        thus ?thesis unfolding Tftm_def comp_def T_def by simp
      qed
    qed
    have hTftm_proj: "\<forall>s\<in>I_set. p0 (Tftm s) = top1_path_power (top1_path_product alpha beta) a m s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "p0 (Tftm s) = p0 (T (ftm s))" unfolding Tftm_def comp_def by simp
      also have "... = p0 (ftm s)" using hT_p0 by simp
      also have "... = top1_path_power (top1_path_product alpha beta) a m s"
        using hftm_proj hs by (by100 blast)
      finally show "p0 (Tftm s) = top1_path_power (top1_path_product alpha beta) a m s" .
    qed
    \<comment> \<open>Concatenate: ftilde_0 * (T \<circ> ftm) from e0 to (a, 2*(m+1)).\<close>
    define ftSm where "ftSm = top1_path_product ftilde_0 Tftm"
    have hftSm_path: "top1_is_path_on E TE e0 (a, 2 * int m + 2) ftSm"
    proof -
      have "top1_is_path_on E TE (a, 0) (a, 2 * int m + 2) ftSm"
        unfolding ftSm_def
        by (rule top1_path_product_is_path[OF hTE])
           (use hft0_path hTftm_path e0_def in auto)
      thus ?thesis unfolding e0_def by simp
    qed
    have h_int_eq: "(2::int) * int m + 2 = 2 + 2 * int m" by linarith
    have hftSm_end: "top1_is_path_on E TE e0 (a, 2 * int (Suc m)) ftSm"
      using hftSm_path by (simp add: h_int_eq algebra_simps)
    have hftSm_proj: "\<forall>s\<in>I_set. p0 (ftSm s) = top1_path_power (top1_path_product alpha beta) a (Suc m) s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (ftSm s) = top1_path_power (top1_path_product alpha beta) a (Suc m) s"
      proof (cases "s \<le> 1/2")
        case True
        have "ftSm s = ftilde_0 (2*s)" unfolding ftSm_def top1_path_product_def using True by simp
        have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        hence "p0 (ftilde_0 (2*s)) = top1_path_product alpha beta (2*s)"
          using hft0_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
            = (top1_path_product alpha beta) (2*s)"
        proof -
          have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
              = top1_path_product (top1_path_product alpha beta)
                  (top1_path_power (top1_path_product alpha beta) a m) s" by simp
          also have "... = (top1_path_product alpha beta) (2*s)"
            unfolding top1_path_product_def using True by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>ftSm s = ftilde_0 (2*s)\<close> unfolding p0_def by simp
      next
        case False
        have "ftSm s = Tftm (2*s - 1)" unfolding ftSm_def top1_path_product_def using False by simp
        have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        hence "p0 (Tftm (2*s - 1)) = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
          using hTftm_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
            = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
        proof -
          have "top1_path_power (top1_path_product alpha beta) a (Suc m) s
              = top1_path_product (top1_path_product alpha beta)
                  (top1_path_power (top1_path_product alpha beta) a m) s" by simp
          also have "... = top1_path_power (top1_path_product alpha beta) a m (2*s - 1)"
            unfolding top1_path_product_def using False by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>ftSm s = Tftm (2*s - 1)\<close> unfolding p0_def by simp
      qed
    qed
    show ?case by (intro exI[of _ ftSm]) (use hftSm_end hftSm_proj in blast)
  qed
  \<comment> \<open>Step 3: g^k lifts to a loop at e0 = (a,0) in E.\<close>
  \<comment> \<open>First get the single g-lift from helix_g_lift_is_loop.\<close>
  have hg1_lift: "\<exists>gt. top1_is_path_on E TE e0 e0 gt \<and>
      (\<forall>s\<in>I_set. p0 (gt s) = top1_path_product gamma delta s)"
  proof -
    \<comment> \<open>Rather than extracting from helix_g_lift_is_loop (whose E'/TE'/p0' would need
       matching to our local E/TE/p0), we directly define the g-lift using the same
       formula as in helix_g_lift_is_loop and prove its properties.\<close>
    define gtilde :: "real \<Rightarrow> ('a \<times> int)" where
      "gtilde = (\<lambda>s. if s \<le> 1/2
        then (gamma (2*s), 0)
        else (let y = delta (2*s - 1) in
              if y \<in> A then (y, 0)
              else if y \<in> B then (y, -2)
              else (y, -1)))"
    have hgt_path: "top1_is_path_on E TE e0 e0 gtilde"
    proof -
      define \<gamma>_lift where "\<gamma>_lift = (\<lambda>s. (gamma s, 0::int))"
      define \<delta>_lift where "\<delta>_lift = (\<lambda>s. let y = delta s in
        if y \<in> A then (y, 0::int) else if y \<in> B then (y, -2::int) else (y, -1::int))"
      have hgt_eq: "gtilde = top1_path_product \<gamma>_lift \<delta>_lift"
        unfolding gtilde_def top1_path_product_def \<gamma>_lift_def \<delta>_lift_def by (rule ext) auto
      have h\<gamma>_lift_path: "top1_is_path_on E TE (a, 0) (a', 0) \<gamma>_lift"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top E TE \<gamma>_lift"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set"
          hence "gamma s \<in> U" using assms(14)
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "\<gamma>_lift s \<in> E" unfolding \<gamma>_lift_def E_def by auto
        next
          fix W assume hW: "W \<in> TE"
          have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
          proof -
            have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
            hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
            thus ?thesis by simp
          qed
          have "{s \<in> I_set. \<gamma>_lift s \<in> W} = {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}"
            hence hs: "s \<in> I_set" and hW': "\<gamma>_lift s \<in> W" by auto
            have "gamma s \<in> U" using assms(14) hs
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
              using hs hW' unfolding \<gamma>_lift_def by auto
          next
            fix s assume "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            thus "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}" unfolding \<gamma>_lift_def by simp
          qed
          moreover have "{s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
          proof -
            have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
              unfolding subspace_topology_def using hslice by blast
            thus ?thesis using assms(14)
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          qed
          ultimately show "{s \<in> I_set. \<gamma>_lift s \<in> W} \<in> I_top" by simp
        qed
      next
        show "\<gamma>_lift 0 = (a, 0)" unfolding \<gamma>_lift_def
          using assms(14) unfolding top1_is_path_on_def by (by100 blast)
      next
        show "\<gamma>_lift 1 = (a', 0)" unfolding \<gamma>_lift_def
          using assms(14) unfolding top1_is_path_on_def by (by100 blast)
      qed
      have h\<delta>_lift_path: "top1_is_path_on E TE (a', 0) (a, 0) \<delta>_lift"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top E TE \<delta>_lift"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume hs: "s \<in> I_set"
          have "delta s \<in> V" using assms(15) hs
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "\<delta>_lift s \<in> E" unfolding \<delta>_lift_def E_def Let_def using assms(5) by auto
        next
          fix W assume hW: "W \<in> TE"
          have hV_slice: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W} \<in> TX"
          proof -
            have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
            hence "{x \<in> A. (x, 2*(-1::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(-1::int)) \<in> W} \<union>
                {x \<in> V-U. (x, 2*(-1::int)+1) \<in> W} \<in> TX" by (rule spec)
            thus ?thesis by simp
          qed
          have heq: "{s \<in> I_set. \<delta>_lift s \<in> W} =
              {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                  {x \<in> V - U. (x, -1::int) \<in> W})}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}"
            hence hs: "s \<in> I_set" and hW': "\<delta>_lift s \<in> W" by auto
            have "delta s \<in> V" using assms(15) hs
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
              using hs hW' assms(5,6) unfolding \<delta>_lift_def Let_def by (auto split: if_splits)
          next
            fix s assume "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
            hence hs: "s \<in> I_set" and hds: "delta s \<in> {x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W}" by auto
            have hAsub: "A \<subseteq> U" and hBsub: "B \<subseteq> U" using assms(5) by (by100 blast)+
            have "\<delta>_lift s \<in> W"
            proof -
              have "delta s \<in> A \<and> (delta s, 0) \<in> W \<or>
                    delta s \<in> B \<and> (delta s, -2) \<in> W \<or>
                    delta s \<in> V - U \<and> (delta s, -1) \<in> W" using hds by (by100 blast)
              thus ?thesis unfolding \<delta>_lift_def Let_def using assms(6) hAsub hBsub
                by (auto split: if_splits)
            qed
            thus "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}" using hs by (by100 blast)
          qed
          have hV_sub_open: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W} \<in> subspace_topology X TX V"
          proof -
            have hsub: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                {x \<in> V - U. (x, -1::int) \<in> W} \<subseteq> V"
              using assms(5) by (by100 blast)
            thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
          qed
          have "{s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W})} \<in> I_top"
            using assms(15) hV_sub_open
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "{s \<in> I_set. \<delta>_lift s \<in> W} \<in> I_top" using heq by simp
        qed
      next
        show "\<delta>_lift 0 = (a', 0)" unfolding \<delta>_lift_def Let_def
          using assms(15) assms(13) assms(6) unfolding top1_is_path_on_def by auto
      next
        show "\<delta>_lift 1 = (a, 0)" unfolding \<delta>_lift_def Let_def
          using assms(15) assms(9) assms(6) unfolding top1_is_path_on_def by auto
      qed
      show ?thesis unfolding hgt_eq e0_def
        by (rule top1_path_product_is_path[OF hTE h\<gamma>_lift_path h\<delta>_lift_path])
    qed
    have hgt_proj: "\<forall>s\<in>I_set. p0 (gtilde s) = top1_path_product gamma delta s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (gtilde s) = top1_path_product gamma delta s"
      proof (cases "s \<le> 1/2")
        case True
        thus ?thesis unfolding gtilde_def p0_def top1_path_product_def by simp
      next
        case False
        define y where "y = delta (2*s - 1)"
        have "gtilde s = (if y \<in> A then (y, 0) else if y \<in> B then (y, -2) else (y, -1))"
          unfolding gtilde_def y_def using False by (simp add: Let_def)
        hence "p0 (gtilde s) = y"
          unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
        thus ?thesis unfolding y_def top1_path_product_def using False by simp
      qed
    qed
    show ?thesis by (intro exI[of _ gtilde]) (use hgt_path hgt_proj in blast)
  qed
  obtain gt1 where hgt1: "top1_is_path_on E TE e0 e0 gt1"
      and hgt1_proj: "\<forall>s\<in>I_set. p0 (gt1 s) = top1_path_product gamma delta s"
    using hg1_lift by (by100 blast)
  \<comment> \<open>By induction: g^k lifts to a loop at e0.\<close>
  have hgk_lift: "\<exists>gtilde_k. top1_is_path_on E TE e0 e0 gtilde_k \<and>
      (\<forall>s\<in>I_set. p0 (gtilde_k s) = top1_path_power (top1_path_product gamma delta) a k s)"
  proof (induction k)
    case 0
    have "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
      by (rule top1_constant_path_is_path[OF hTE he0_E])
    moreover have "\<forall>s\<in>I_set. p0 (top1_constant_path e0 s) = top1_path_power (top1_path_product gamma delta) a 0 s"
    proof
      fix s assume "s \<in> I_set"
      have "p0 (top1_constant_path e0 s) = p0 e0" unfolding top1_constant_path_def by simp
      also have "... = a" using hp0e0 by simp
      also have "... = top1_constant_path a s" unfolding top1_constant_path_def by simp
      also have "... = top1_path_power (top1_path_product gamma delta) a 0 s" by simp
      finally show "p0 (top1_constant_path e0 s) = top1_path_power (top1_path_product gamma delta) a 0 s" .
    qed
    ultimately show ?case by (intro exI[of _ "top1_constant_path e0"]) (by100 blast)
  next
    case (Suc k)
    obtain gtk where hgtk: "top1_is_path_on E TE e0 e0 gtk"
        and hgtk_proj: "\<forall>s\<in>I_set. p0 (gtk s) = top1_path_power (top1_path_product gamma delta) a k s"
      using Suc by (by100 blast)
    define gtSk where "gtSk = top1_path_product gt1 gtk"
    have hgtSk: "top1_is_path_on E TE e0 e0 gtSk"
      unfolding gtSk_def by (rule top1_path_product_is_path[OF hTE hgt1 hgtk])
    have hgtSk_proj: "\<forall>s\<in>I_set. p0 (gtSk s) = top1_path_power (top1_path_product gamma delta) a (Suc k) s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (gtSk s) = top1_path_power (top1_path_product gamma delta) a (Suc k) s"
      proof (cases "s \<le> 1/2")
        case True
        have "gtSk s = gt1 (2*s)" unfolding gtSk_def top1_path_product_def using True by simp
        have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        hence "p0 (gt1 (2*s)) = top1_path_product gamma delta (2*s)"
          using hgt1_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product gamma delta) a (Suc k) s
            = top1_path_product gamma delta (2*s)"
        proof -
          have "top1_path_power (top1_path_product gamma delta) a (Suc k) s
              = top1_path_product (top1_path_product gamma delta)
                  (top1_path_power (top1_path_product gamma delta) a k) s" by simp
          also have "... = (top1_path_product gamma delta) (2*s)"
            unfolding top1_path_product_def using True by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>gtSk s = gt1 (2*s)\<close> unfolding p0_def by simp
      next
        case False
        have hs_half: "s > 1/2" using False by simp
        have "gtSk s = gtk (2*s - 1)" unfolding gtSk_def top1_path_product_def using False by simp
        have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        hence "p0 (gtk (2*s - 1)) = top1_path_power (top1_path_product gamma delta) a k (2*s - 1)"
          using hgtk_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_product gamma delta) a (Suc k) s
            = top1_path_power (top1_path_product gamma delta) a k (2*s - 1)"
        proof -
          have "top1_path_power (top1_path_product gamma delta) a (Suc k) s
              = top1_path_product (top1_path_product gamma delta)
                  (top1_path_power (top1_path_product gamma delta) a k) s" by simp
          also have "... = top1_path_power (top1_path_product gamma delta) a k (2*s - 1)"
            unfolding top1_path_product_def using False by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>gtSk s = gtk (2*s - 1)\<close> unfolding p0_def by simp
      qed
    qed
    show ?case by (intro exI[of _ gtSk]) (use hgtSk hgtSk_proj in blast)
  qed
  \<comment> \<open>Step 4: By Theorem_54_3, since [f]^m = [g]^k (path-homotopic),
     the lifts have the same endpoint: (a, 2*(int m)) = (a, 0) = e0.\<close>
  obtain ftilde_m where hft: "top1_is_path_on E TE e0 (a, 2 * int m) ftilde_m"
      and hft_proj: "\<forall>s\<in>I_set. p0 (ftilde_m s) = top1_path_power (top1_path_product alpha beta) a m s"
    using hfm_lift by (by100 blast)
  obtain gtilde_k where hgt: "top1_is_path_on E TE e0 e0 gtilde_k"
      and hgt_proj: "\<forall>s\<in>I_set. p0 (gtilde_k s) = top1_path_power (top1_path_product gamma delta) a k s"
    using hgk_lift by (by100 blast)
  have hf_loop_X: "top1_is_loop_on X TX a (top1_path_product alpha beta)"
  proof -
    have h\<alpha>_X: "top1_is_path_on X TX a b alpha"
      by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(2) assms(11)])
         (use assms(4) in blast)
    have h\<beta>_X: "top1_is_path_on X TX b a beta"
      by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(3) assms(12)])
         (use assms(4) in blast)
    show ?thesis unfolding top1_is_loop_on_def
      using top1_path_product_is_path[OF assms(1) h\<alpha>_X h\<beta>_X] by simp
  qed
  have hg_loop_X: "top1_is_loop_on X TX a (top1_path_product gamma delta)"
  proof -
    have h\<gamma>_X: "top1_is_path_on X TX a a' gamma"
      by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(2) assms(14)])
         (use assms(4) in blast)
    have h\<delta>_X: "top1_is_path_on X TX a' a delta"
      by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(3) assms(15)])
         (use assms(4) in blast)
    show ?thesis unfolding top1_is_loop_on_def
      using top1_path_product_is_path[OF assms(1) h\<gamma>_X h\<delta>_X] by simp
  qed
  have hfm_path: "top1_is_path_on X TX a a (top1_path_power (top1_path_product alpha beta) a m)"
    by (rule top1_path_power_is_path[OF assms(1) hf_loop_X])
  have hgk_path: "top1_is_path_on X TX a a (top1_path_power (top1_path_product gamma delta) a k)"
    by (rule top1_path_power_is_path[OF assms(1) hg_loop_X])
  have "e0 = (a, 2 * int m)"
  proof -
    have heq: "(a, 2 * int m) = e0 \<and>
        top1_path_homotopic_on E TE e0 (a, 2 * int m) ftilde_m gtilde_k"
      by (rule Theorem_54_3[OF hcov hTE assms(1) he0_E hp0e0
          hfm_path hgk_path assms(16) hft hft_proj hgt hgt_proj])
    thus ?thesis by simp
  qed
  hence "2 * int m = (0::int)" unfolding e0_def by simp
  hence "m = 0" by simp
  thus False using hm by simp
qed

\<comment> \<open>Abstract endpoint lemma: if f^m lifts from e0 to (a,2m) and h^k lifts to a loop at e0,
   and [f^m] \<simeq> [h^k], then m = 0 by Theorem_54_3.\<close>
lemma covering_lift_endpoint_contradiction:
  assumes "top1_covering_map_on E TE X TX p0"
      and "is_topology_on E TE" and "is_topology_on X TX"
      and "(a, 0::int) \<in> E" and "p0 (a, 0::int) = a"
      \<comment> \<open>f^m lifts from (a,0) to (a, 2*int m).\<close>
      and "top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm"
      and "\<forall>s\<in>I_set. p0 (ftm s) = fm s"
      and "top1_is_path_on X TX a a fm"
      \<comment> \<open>h^k lifts to a LOOP at (a,0).\<close>
      and "top1_is_path_on E TE (a, 0) (a, 0) hkl"
      and "\<forall>s\<in>I_set. p0 (hkl s) = hk s"
      and "top1_is_path_on X TX a a hk"
      \<comment> \<open>f^m \<simeq> h^k.\<close>
      and "top1_path_homotopic_on X TX a a fm hk"
  shows "m = 0"
proof -
  have "(a, 2 * int m) = (a, 0::int)"
    using conjunct1[OF Theorem_54_3[OF assms(1-5,8,11,12,6,7,9,10)]] by simp
  hence "2 * int m = (0::int)" by simp
  thus ?thesis by simp
qed

\<comment> \<open>63.1(c) for the reverse loop g\<inverse>: same helix, reverse g-lift is a loop.\<close>
lemma Theorem_63_1_c_subgroups_trivial_reverse:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
      and "a' \<in> A"
      and "top1_is_path_on U (subspace_topology X TX U) a a' gamma"
      and "top1_is_path_on V (subspace_topology X TX V) a' a delta"
      and "top1_path_homotopic_on X TX a a
            (top1_path_power (top1_path_product alpha beta) a m)
            (top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k)"
  shows "m = 0"
proof -
  \<comment> \<open>Build helix (same as 63.1(c)).\<close>
  have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
  define E :: "('a \<times> int) set" where
    "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
  define TE :: "('a \<times> int) set set" where
    "TE = {W. W \<subseteq> E \<and>
      (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
      (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
  define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
  have he0: "(a, 0::int) \<in> E" unfolding E_def using ha_U by simp
  have hp0: "p0 (a, 0::int) = a" unfolding p0_def by simp
  have hcov_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
  proof -
    note h = helix_covering_construction[OF assms(1-8)]
    have "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
      unfolding E_def by auto
    moreover have "TE = {W. W \<subseteq> E \<and>
        (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
        (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
              {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
      unfolding TE_def E_def by auto
    moreover have "p0 = fst" unfolding p0_def by simp
    ultimately show ?thesis using h by simp
  qed
  hence hTE: "is_topology_on E TE" and hcov: "top1_covering_map_on E TE X TX p0" by auto
  \<comment> \<open>f^m lift from (a,0) to (a,2m). Same construction as in Theorem_63_1_c.\<close>
  have hfm_lift: "\<exists>ftm. top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm \<and>
      (\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s)"
  proof (rule helix_f_power_lift[OF assms(1-12) hcov hTE he0 hp0])
    show "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> U. (x, 2 * n) \<in> W} \<in> TX"
      unfolding TE_def by (by100 blast)
    show "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
        {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX"
      unfolding TE_def by (by100 blast)
    show "\<And>x n. x \<in> U \<Longrightarrow> (x, 2*n) \<in> E" unfolding E_def by auto
    show "\<And>x n. x \<in> V - U \<Longrightarrow> (x, 2*n + 1) \<in> E" unfolding E_def by auto
    show "\<And>x n. x \<in> A \<Longrightarrow> (x, 2*n + 2) \<in> E"
    proof -
      fix x :: 'a and n :: int assume "x \<in> A"
      hence "x \<in> U" using assms(5) by (by100 blast)
      thus "(x, 2*n + 2) \<in> E" unfolding E_def by auto
    qed
    show "\<And>x n. x \<in> B \<Longrightarrow> (x, 2*n) \<in> E"
    proof -
      fix x :: 'a and n :: int assume "x \<in> B"
      hence "x \<in> U" using assms(5) by (by100 blast)
      thus "(x, 2*n) \<in> E" unfolding E_def by auto
    qed
    show "p0 = fst" unfolding p0_def by simp
    show "\<And>x m. (x, m) \<in> E \<Longrightarrow> (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)"
      unfolding E_def by auto
    show "\<And>W. \<lbrakk>W \<subseteq> E; \<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX;
        \<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                  {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX\<rbrakk> \<Longrightarrow> W \<in> TE"
      unfolding TE_def by (by100 blast)
  qed
  \<comment> \<open>(g\<inverse>)^k lift: reverse of g-lift is a loop at (a,0), projects to g\<inverse>.
     By induction, (g\<inverse>)^k lifts to a loop at (a,0).\<close>
  \<comment> \<open>Construct single g-lift directly (same formula as in 63.1(c) proof).\<close>
  define gtilde :: "real \<Rightarrow> ('a \<times> int)" where
    "gtilde = (\<lambda>s. if s \<le> 1/2 then (gamma (2*s), 0)
      else (let y = delta (2*s - 1) in
            if y \<in> A then (y, 0) else if y \<in> B then (y, -2) else (y, -1)))"
  have hg1_lift: "\<exists>gt. top1_is_path_on E TE (a, 0) (a, 0) gt \<and>
      (\<forall>s\<in>I_set. p0 (gt s) = top1_path_product gamma delta s)"
  proof (intro exI[of _ gtilde] conjI)
    show "top1_is_path_on E TE (a, 0) (a, 0) gtilde"
    proof -
      define \<gamma>_lift where "\<gamma>_lift = (\<lambda>s. (gamma s, 0::int))"
      define \<delta>_lift where "\<delta>_lift = (\<lambda>s. let y = delta s in
        if y \<in> A then (y, 0::int) else if y \<in> B then (y, -2::int) else (y, -1::int))"
      have hgt_eq: "gtilde = top1_path_product \<gamma>_lift \<delta>_lift"
        unfolding gtilde_def top1_path_product_def \<gamma>_lift_def \<delta>_lift_def by (rule ext) auto
      have h\<gamma>_lift_path: "top1_is_path_on E TE (a, 0) (a', 0) \<gamma>_lift"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top E TE \<gamma>_lift"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set"
          hence "gamma s \<in> U" using assms(14)
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "\<gamma>_lift s \<in> E" unfolding \<gamma>_lift_def E_def by auto
        next
          fix W assume hW: "W \<in> TE"
          have hslice: "{x \<in> U. (x, 0::int) \<in> W} \<in> TX"
          proof -
            have "\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
            hence "{x \<in> U. (x, 2*(0::int)) \<in> W} \<in> TX" by (rule spec)
            thus ?thesis by simp
          qed
          have "{s \<in> I_set. \<gamma>_lift s \<in> W} = {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}"
            hence hs: "s \<in> I_set" and hW': "\<gamma>_lift s \<in> W" by auto
            have "gamma s \<in> U" using assms(14) hs
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
              using hs hW' unfolding \<gamma>_lift_def by auto
          next
            fix s assume "s \<in> {s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}}"
            thus "s \<in> {s \<in> I_set. \<gamma>_lift s \<in> W}" unfolding \<gamma>_lift_def by simp
          qed
          moreover have "{s \<in> I_set. gamma s \<in> {x \<in> U. (x, 0::int) \<in> W}} \<in> I_top"
          proof -
            have "{x \<in> U. (x, 0::int) \<in> W} \<in> subspace_topology X TX U"
              unfolding subspace_topology_def using hslice by blast
            thus ?thesis using assms(14)
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          qed
          ultimately show "{s \<in> I_set. \<gamma>_lift s \<in> W} \<in> I_top" by simp
        qed
      next
        show "\<gamma>_lift 0 = (a, 0)" unfolding \<gamma>_lift_def
          using assms(14) unfolding top1_is_path_on_def by (by100 blast)
      next
        show "\<gamma>_lift 1 = (a', 0)" unfolding \<gamma>_lift_def
          using assms(14) unfolding top1_is_path_on_def by (by100 blast)
      qed
      have h\<delta>_lift_path: "top1_is_path_on E TE (a', 0) (a, 0) \<delta>_lift"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top E TE \<delta>_lift"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume hs: "s \<in> I_set"
          have "delta s \<in> V" using assms(15) hs
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "\<delta>_lift s \<in> E" unfolding \<delta>_lift_def E_def Let_def using assms(5) by auto
        next
          fix W assume hW: "W \<in> TE"
          have hV_slice: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W} \<in> TX"
          proof -
            have "\<forall>n::int. {x \<in> A. (x, 2*n+2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V-U. (x, 2*n+1) \<in> W} \<in> TX" using hW unfolding TE_def by (by100 blast)
            hence "{x \<in> A. (x, 2*(-1::int)+2) \<in> W} \<union> {x \<in> B. (x, 2*(-1::int)) \<in> W} \<union>
                {x \<in> V-U. (x, 2*(-1::int)+1) \<in> W} \<in> TX" by (rule spec)
            thus ?thesis by simp
          qed
          have heq: "{s \<in> I_set. \<delta>_lift s \<in> W} =
              {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                  {x \<in> V - U. (x, -1::int) \<in> W})}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}"
            hence hs: "s \<in> I_set" and hW': "\<delta>_lift s \<in> W" by auto
            have "delta s \<in> V" using assms(15) hs
              unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
            thus "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
              using hs hW' assms(5,6) unfolding \<delta>_lift_def Let_def by (auto split: if_splits)
          next
            fix s assume "s \<in> {s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W})}"
            hence hs: "s \<in> I_set" and hds: "delta s \<in> {x \<in> A. (x, 0::int) \<in> W} \<union>
                {x \<in> B. (x, -2::int) \<in> W} \<union> {x \<in> V - U. (x, -1::int) \<in> W}" by auto
            have hAsub: "A \<subseteq> U" and hBsub: "B \<subseteq> U" using assms(5) by (by100 blast)+
            have "\<delta>_lift s \<in> W"
            proof -
              have "delta s \<in> A \<and> (delta s, 0) \<in> W \<or>
                    delta s \<in> B \<and> (delta s, -2) \<in> W \<or>
                    delta s \<in> V - U \<and> (delta s, -1) \<in> W" using hds by (by100 blast)
              thus ?thesis unfolding \<delta>_lift_def Let_def using assms(6) hAsub hBsub
                by (auto split: if_splits)
            qed
            thus "s \<in> {s \<in> I_set. \<delta>_lift s \<in> W}" using hs by (by100 blast)
          qed
          have hV_sub_open: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W} \<in> subspace_topology X TX V"
          proof -
            have hsub: "{x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
                {x \<in> V - U. (x, -1::int) \<in> W} \<subseteq> V"
              using assms(5) by (by100 blast)
            thus ?thesis using hV_slice unfolding subspace_topology_def by (by100 blast)
          qed
          have "{s \<in> I_set. delta s \<in> ({x \<in> A. (x, 0::int) \<in> W} \<union> {x \<in> B. (x, -2::int) \<in> W} \<union>
              {x \<in> V - U. (x, -1::int) \<in> W})} \<in> I_top"
            using assms(15) hV_sub_open
            unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          thus "{s \<in> I_set. \<delta>_lift s \<in> W} \<in> I_top" using heq by simp
        qed
      next
        show "\<delta>_lift 0 = (a', 0)" unfolding \<delta>_lift_def Let_def
          using assms(15) assms(13) assms(6) unfolding top1_is_path_on_def by auto
      next
        show "\<delta>_lift 1 = (a, 0)" unfolding \<delta>_lift_def Let_def
          using assms(15) assms(9) assms(6) unfolding top1_is_path_on_def by auto
      qed
      show ?thesis unfolding hgt_eq
        by (rule top1_path_product_is_path[OF hTE h\<gamma>_lift_path h\<delta>_lift_path])
    qed
    show "\<forall>s\<in>I_set. p0 (gtilde s) = top1_path_product gamma delta s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (gtilde s) = top1_path_product gamma delta s"
      proof (cases "s \<le> 1/2")
        case True thus ?thesis unfolding gtilde_def p0_def top1_path_product_def by simp
      next
        case False
        define y where "y = delta (2*s - 1)"
        have "gtilde s = (if y \<in> A then (y, 0) else if y \<in> B then (y, -2) else (y, -1))"
          unfolding gtilde_def y_def using False by (simp add: Let_def)
        hence "p0 (gtilde s) = y"
          unfolding p0_def by (cases "y \<in> A"; cases "y \<in> B"; simp)
        thus ?thesis unfolding y_def top1_path_product_def using False by simp
      qed
    qed
  qed
  obtain gt where hgt: "top1_is_path_on E TE (a, 0) (a, 0) gt"
      and hgt_proj: "\<forall>s\<in>I_set. p0 (gt s) = top1_path_product gamma delta s"
    using hg1_lift by (by100 blast)
  \<comment> \<open>Reverse g-lift: loop at (a,0), projects to g\<inverse>.\<close>
  define gt_rev where "gt_rev = top1_path_reverse gt"
  have hgt_rev_path: "top1_is_path_on E TE (a, 0) (a, 0) gt_rev"
  proof -
    have "top1_is_path_on E TE (a, 0) (a, 0) (top1_path_reverse gt)"
      using top1_path_reverse_is_path[OF hgt] hgt
      unfolding top1_is_path_on_def top1_path_reverse_def by auto
    thus ?thesis unfolding gt_rev_def by simp
  qed
  have hgt_rev_proj: "\<forall>s\<in>I_set. p0 (gt_rev s) = top1_path_reverse (top1_path_product gamma delta) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "1 - s \<in> I_set" using hs unfolding top1_unit_interval_def by auto
    show "p0 (gt_rev s) = top1_path_reverse (top1_path_product gamma delta) s"
      unfolding gt_rev_def top1_path_reverse_def using hgt_proj \<open>1 - s \<in> I_set\<close> p0_def by auto
  qed
  \<comment> \<open>By induction: (g\<inverse>)^k lifts to a loop at (a,0).\<close>
  have hginvk_lift: "\<exists>gkl. top1_is_path_on E TE (a, 0) (a, 0) gkl \<and>
      (\<forall>s\<in>I_set. p0 (gkl s) = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k s)"
  proof (induction k)
    case 0
    have "top1_is_path_on E TE (a, 0) (a, 0) (top1_constant_path (a, 0))"
      by (rule top1_constant_path_is_path[OF hTE he0])
    moreover have "\<forall>s\<in>I_set. p0 (top1_constant_path (a, 0) s) =
        top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a 0 s"
      by (simp add: top1_constant_path_def hp0)
    ultimately show ?case by (intro exI[of _ "top1_constant_path (a, 0)"]) auto
  next
    case (Suc k)
    obtain gkl where hgkl_k: "top1_is_path_on E TE (a, 0) (a, 0) gkl"
        and hgkl_proj_k: "\<forall>s\<in>I_set. p0 (gkl s) =
            top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k s"
      using Suc by (by100 blast)
    define gSk where "gSk = top1_path_product gt_rev gkl"
    have "top1_is_path_on E TE (a, 0) (a, 0) gSk"
      unfolding gSk_def by (rule top1_path_product_is_path[OF hTE hgt_rev_path hgkl_k])
    moreover have "\<forall>s\<in>I_set. p0 (gSk s) =
        top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "p0 (gSk s) = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s"
      proof (cases "s \<le> 1/2")
        case True
        have "gSk s = gt_rev (2*s)" unfolding gSk_def top1_path_product_def using True by simp
        have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        hence "p0 (gt_rev (2*s)) = top1_path_reverse (top1_path_product gamma delta) (2*s)"
          using hgt_rev_proj by (by100 blast)
        moreover have "top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s
            = top1_path_reverse (top1_path_product gamma delta) (2*s)"
        proof -
          have "top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s
              = top1_path_product (top1_path_reverse (top1_path_product gamma delta))
                  (top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k) s" by simp
          also have "... = (top1_path_reverse (top1_path_product gamma delta)) (2*s)"
            unfolding top1_path_product_def using True by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>gSk s = gt_rev (2*s)\<close> unfolding p0_def by simp
      next
        case False
        have "gSk s = gkl (2*s - 1)" unfolding gSk_def top1_path_product_def using False by simp
        have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        hence "p0 (gkl (2*s - 1)) = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k (2*s - 1)"
          using hgkl_proj_k by (by100 blast)
        moreover have "top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s
            = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k (2*s - 1)"
        proof -
          have "top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a (Suc k) s
              = top1_path_product (top1_path_reverse (top1_path_product gamma delta))
                  (top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k) s" by simp
          also have "... = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k (2*s - 1)"
            unfolding top1_path_product_def using False by simp
          finally show ?thesis .
        qed
        ultimately show ?thesis using \<open>gSk s = gkl (2*s - 1)\<close> unfolding p0_def by simp
      qed
    qed
    ultimately show ?case by (intro exI[of _ gSk]) (by100 blast)
  qed
  \<comment> \<open>Apply covering_lift_endpoint_contradiction.\<close>
  obtain ftm where hftm: "top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm"
      and hftm_proj: "\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product alpha beta) a m s"
    using hfm_lift by (by100 blast)
  obtain gkl where hgkl: "top1_is_path_on E TE (a, 0) (a, 0) gkl"
      and hgkl_proj: "\<forall>s\<in>I_set. p0 (gkl s) = top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k s"
    using hginvk_lift by (by100 blast)
  have hfm_path: "top1_is_path_on X TX a a (top1_path_power (top1_path_product alpha beta) a m)"
  proof -
    have hf_loop: "top1_is_loop_on X TX a (top1_path_product alpha beta)"
    proof -
      have "top1_is_path_on X TX a b alpha"
        by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(2) assms(11)])
           (use assms(4) in blast)
      moreover have "top1_is_path_on X TX b a beta"
        by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(3) assms(12)])
           (use assms(4) in blast)
      ultimately show ?thesis unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF assms(1)] by (by100 blast)
    qed
    show ?thesis by (rule top1_path_power_is_path[OF assms(1) hf_loop])
  qed
  have hginvk_path: "top1_is_path_on X TX a a
      (top1_path_power (top1_path_reverse (top1_path_product gamma delta)) a k)"
  proof -
    have hg_path: "top1_is_path_on X TX a a (top1_path_product gamma delta)"
    proof -
      have "top1_is_path_on X TX a a' gamma"
        by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(2) assms(14)])
           (use assms(4) in blast)
      moreover have "top1_is_path_on X TX a' a delta"
        by (rule path_in_subspace_is_path_in_space[OF assms(1) _ assms(3) assms(15)])
           (use assms(4) in blast)
      ultimately show ?thesis using top1_path_product_is_path[OF assms(1)] by (by100 blast)
    qed
    have hginv_loop: "top1_is_loop_on X TX a (top1_path_reverse (top1_path_product gamma delta))"
    proof -
      have "top1_is_path_on X TX a a (top1_path_reverse (top1_path_product gamma delta))"
        using top1_path_reverse_is_path[OF hg_path] hg_path
        unfolding top1_is_path_on_def top1_path_reverse_def by auto
      thus ?thesis unfolding top1_is_loop_on_def by simp
    qed
    show ?thesis by (rule top1_path_power_is_path[OF assms(1) hginv_loop])
  qed
  show "m = 0"
    by (rule covering_lift_endpoint_contradiction[OF hcov hTE assms(1) he0 hp0
        hftm hftm_proj hfm_path hgkl hgkl_proj hginvk_path assms(16)])
qed

\<comment> \<open>Corollary for 63.5: In the setting of 63.1 on S^2-{p,q}, if we have two loops f and g
   where f = \<alpha>*\<beta> and g = \<gamma>*\<delta> (constructed from different component decompositions),
   both nontrivial, the fact that \<pi>_1(S^2-{p,q}) \<cong> Z forces [f]^m = [g]^k for some
   nonzero m,k. But 63.1(c) says m must be 0. Contradiction.\<close>
lemma pi1_S2_minus_two_points_infinite_cyclic:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "p \<in> top1_S2" and "q \<in> top1_S2" and "p \<noteq> q"
      and "a \<in> top1_S2 - {p} - {q}"
  shows "\<exists>gen. top1_is_loop_on (top1_S2 - {p} - {q})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) a gen \<and>
    (\<forall>f. top1_is_loop_on (top1_S2 - {p} - {q})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) a f \<longrightarrow>
      (\<exists>n::nat. top1_path_homotopic_on (top1_S2 - {p} - {q})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) a a
        f (top1_path_power gen a n) \<or>
       top1_path_homotopic_on (top1_S2 - {p} - {q})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) a a
        f (top1_path_power (top1_path_reverse gen) a n)))"
proof -
  \<comment> \<open>Chain: S^2-{p} \<cong> R^2 (stereographic), S^2-{p,q} \<cong> R^2-{h(q)},
     R^2-{point} deformation retracts to S^1, \<pi>_1(S^1) \<cong> Z (Theorem_54_5_iso).\<close>
  let ?X = "top1_S2 - {p} - {q}" and ?TX = "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})"
  \<comment> \<open>Step 1: Stereographic projection \<sigma> from p gives S^2-{p} \<cong> R^2.\<close>
  obtain \<sigma> where h\<sigma>: "top1_homeomorphism_on (top1_S2 - {p})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
      (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) \<sigma>"
    using S2_minus_point_homeo_R2[OF assms(2)] by blast
  \<comment> \<open>Step 2: Restrict to S^2-{p,q}: \<sigma> maps this to R^2-{\<sigma>(q)}.\<close>
  define q' where "q' = \<sigma> q"
  have hq_in: "q \<in> top1_S2 - {p}" using assms(3,4) by (by100 blast)
  have ha_in: "a \<in> top1_S2 - {p}" using assms(5) by (by100 blast)
  define a' where "a' = \<sigma> a"
  \<comment> \<open>Step 3: \<sigma> restricts to homeomorphism S^2-{p,q} \<cong> R^2-{q'}.\<close>
  \<comment> \<open>Step 4: R^2-{q'} is homeomorphic to R^2-{0} (by translation).\<close>
  \<comment> \<open>Step 5: R^2-{0} deformation retracts to S^1 (Theorem_58_2_inclusion_iso).\<close>
  \<comment> \<open>Step 6: \<pi>_1(S^1) \<cong> Z (Theorem_54_5_iso).\<close>
  \<comment> \<open>Step 7: Chain of isomorphisms: \<pi>_1(S^2-{p,q}) \<cong> \<pi>_1(R^2-{q'}) \<cong> \<pi>_1(R^2-{0}) \<cong> \<pi>_1(S^1) \<cong> Z.\<close>
  \<comment> \<open>Step 8: Extract generator and generate-all property.\<close>
  \<comment> \<open>Step 3: \<sigma> restricts to homeomorphism ?X \<cong> R^2-{q'}.\<close>
  define R2_q' :: "(real \<times> real) set" where "R2_q' = UNIV - {q'}"
  define TR2_q' where "TR2_q' = subspace_topology UNIV
      (product_topology_on top1_open_sets top1_open_sets) R2_q'"
  have h\<sigma>_restrict: "top1_homeomorphism_on ?X ?TX R2_q' TR2_q' \<sigma>"
  proof -
    have h_step: "top1_homeomorphism_on ((top1_S2 - {p}) - {q})
        (subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
          ((top1_S2 - {p}) - {q}))
        ((UNIV :: (real \<times> real) set) - {\<sigma> q})
        (subspace_topology (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)
          (UNIV - {\<sigma> q})) \<sigma>"
      by (rule homeomorphism_restrict_point[OF h\<sigma> hq_in])
    \<comment> \<open>Simplify: (S^2-{p})-{q} = S^2-{p}-{q} = ?X, subspace of subspace = subspace.\<close>
    have hX_eq: "(top1_S2 - {p}) - {q} = ?X" by (by100 blast)
    have hY_eq: "(UNIV :: (real \<times> real) set) - {\<sigma> q} = R2_q'" unfolding R2_q'_def q'_def by simp
    have hTX_eq: "subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
        ((top1_S2 - {p}) - {q}) = ?TX"
    proof -
      have "?X \<subseteq> top1_S2 - {p}" by (by100 blast)
      hence "subspace_topology (top1_S2 - {p}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p}))
          ?X = subspace_topology top1_S2 top1_S2_topology ?X"
        by (rule subspace_topology_trans)
      moreover have "(top1_S2 - {p}) - {q} = ?X" by (by100 blast)
      ultimately show ?thesis by simp
    qed
    have hTY_eq: "subspace_topology (UNIV :: (real \<times> real) set)
        (product_topology_on top1_open_sets top1_open_sets) (UNIV - {\<sigma> q}) = TR2_q'"
      unfolding TR2_q'_def R2_q'_def q'_def by simp
    show ?thesis using h_step hX_eq hY_eq hTX_eq hTY_eq by simp
  qed
  \<comment> \<open>Step 4: Translation t(x) = x - q' gives R^2-{q'} \<cong> R^2-{0}.\<close>
  define R2_0 :: "(real \<times> real) set" where "R2_0 = UNIV - {(0, 0)}"
  define TR2_0 where "TR2_0 = subspace_topology UNIV
      (product_topology_on top1_open_sets top1_open_sets) R2_0"
  define t :: "real \<times> real \<Rightarrow> real \<times> real" where
    "t = (\<lambda>(x, y). (x - fst q', y - snd q'))"
  have ht_homeo: "top1_homeomorphism_on R2_q' TR2_q' R2_0 TR2_0 t"
  proof -
    have ht_eq: "t = (\<lambda>x. (fst x - fst q', snd x - snd q'))"
      unfolding t_def by (rule ext) auto
    show ?thesis unfolding R2_q'_def TR2_q'_def R2_0_def TR2_0_def ht_eq
      by (rule translation_homeo_R2[of q'])
  qed
  \<comment> \<open>Step 5-6: \<pi>_1(R^2-{0}) \<cong> \<pi>_1(S^1) \<cong> Z. Use existing Theorem_58_2 + Theorem_54_5.\<close>
  \<comment> \<open>Step 7: Chain: \<pi>_1(S^2-{p,q}) \<cong> \<pi>_1(R^2-{q'}) \<cong> \<pi>_1(R^2-{0}) \<cong> \<pi>_1(S^1) \<cong> Z.
     The composition \<sigma> ; t maps a \<in> S^2-{p,q} to t(\<sigma>(a)) \<in> R^2-{0}.
     By Theorem_58_7, the induced map on \<pi>_1 is an isomorphism.\<close>
  \<comment> \<open>Step 8: Extract generator from the isomorphism with Z and convert to path_power form.\<close>
  \<comment> \<open>Step 5: Compose \<sigma> and t to get homeomorphism X \<rightarrow> R^2-{0}.\<close>
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF
        is_topology_on_strict_imp[OF assms(1)]]) (by100 blast)
  have hTR2_0: "is_topology_on R2_0 TR2_0"
    unfolding TR2_0_def R2_0_def
    by (rule subspace_topology_is_topology_on[OF
        product_topology_on_is_topology_on[OF
          top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
          simplified]]) (by100 simp)
  define h where "h = t \<circ> \<sigma>"
  have hh_homeo: "top1_homeomorphism_on ?X ?TX R2_0 TR2_0 h"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on ?X ?TX" by (rule hTX)
    show "is_topology_on R2_0 TR2_0" by (rule hTR2_0)
    show "bij_betw h ?X R2_0"
    proof -
      have "bij_betw \<sigma> ?X R2_q'" using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
      moreover have "bij_betw t R2_q' R2_0" using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      ultimately show ?thesis unfolding h_def using bij_betw_comp_iff by (by100 blast)
    qed
    show "top1_continuous_map_on ?X ?TX R2_0 TR2_0 h"
    proof -
      have h1: "top1_continuous_map_on ?X ?TX R2_q' TR2_q' \<sigma>"
        using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
      have h2: "top1_continuous_map_on R2_q' TR2_q' R2_0 TR2_0 t"
        using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      show ?thesis unfolding h_def by (rule top1_continuous_map_on_comp[OF h1 h2])
    qed
    show "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X h)"
    proof -
      have hinv_\<sigma>: "top1_continuous_map_on R2_q' TR2_q' ?X ?TX (inv_into ?X \<sigma>)"
        using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinv_t: "top1_continuous_map_on R2_0 TR2_0 R2_q' TR2_q' (inv_into R2_q' t)"
        using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hcomp_inv: "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X \<sigma> \<circ> inv_into R2_q' t)"
        by (rule top1_continuous_map_on_comp[OF hinv_t hinv_\<sigma>])
      \<comment> \<open>inv_into X (t \<circ> \<sigma>) = inv_into X \<sigma> \<circ> inv_into R2_q' t on R2_0.\<close>
      \<comment> \<open>inv_into X h continuous: show preimage of TX-open under inv_into = h-image is TR2_0-open.
         h = t \<circ> \<sigma>, both open maps (homeomorphisms), so h is an open map.\<close>
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix y assume "y \<in> R2_0"
        have hbij: "bij_betw h ?X R2_0"
        proof -
          have "bij_betw \<sigma> ?X R2_q'" using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
          moreover have "bij_betw t R2_q' R2_0" using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          ultimately show ?thesis unfolding h_def using bij_betw_comp_iff by (by100 blast)
        qed
        have "y \<in> h ` ?X" using \<open>y \<in> R2_0\<close> hbij unfolding bij_betw_def by (by100 blast)
        thus "inv_into ?X h y \<in> ?X" using inv_into_into[OF \<open>y \<in> h ` ?X\<close>] by (by100 blast)
      next
        fix W assume "W \<in> ?TX"
        \<comment> \<open>Need: {y \<in> R2_0. inv_into X h y \<in> W} \<in> TR2_0.
           This equals h ` (W \<inter> X) = h ` W (since W \<subseteq> X from topology).
           h ` W = t ` (\<sigma> ` W). \<sigma> ` W is open in TR2_q' (σ is open map).
           t ` (\<sigma> ` W) is open in TR2_0 (t is open map).\<close>
        have hbij: "bij_betw h ?X R2_0"
        proof -
          have "bij_betw \<sigma> ?X R2_q'" using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
          moreover have "bij_betw t R2_q' R2_0" using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          ultimately show ?thesis unfolding h_def using bij_betw_comp_iff by (by100 blast)
        qed
        \<comment> \<open>{y \<in> R2_0 | inv h y \<in> W} = h ` W (since h bijection X \<rightarrow> R2_0).\<close>
        have hW_sub: "W \<subseteq> ?X"
        proof -
          have "?TX = subspace_topology top1_S2 top1_S2_topology ?X" by (by100 simp)
          then obtain W0 where "W0 \<in> top1_S2_topology" "W = ?X \<inter> W0"
            using \<open>W \<in> ?TX\<close> unfolding subspace_topology_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have heq: "{y \<in> R2_0. inv_into ?X h y \<in> W} = h ` W"
        proof (rule set_eqI, rule iffI)
          fix y assume "y \<in> {y \<in> R2_0. inv_into ?X h y \<in> W}"
          hence hy: "y \<in> R2_0" and hinv: "inv_into ?X h y \<in> W" by (by100 auto)
          have "y \<in> h ` ?X" using hy hbij unfolding bij_betw_def by (by100 blast)
          have "y = h (inv_into ?X h y)" using f_inv_into_f[OF \<open>y \<in> h ` ?X\<close>] by (by100 simp)
          thus "y \<in> h ` W" using hinv by (by100 blast)
        next
          fix y assume "y \<in> h ` W"
          then obtain x where hx: "x \<in> W" "y = h x" by (by100 blast)
          have "x \<in> ?X" using hx(1) hW_sub by (by100 blast)
          hence "inv_into ?X h y = x"
            using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij] \<open>x \<in> ?X\<close>] hx(2) by (by100 simp)
          moreover have "y \<in> R2_0" using hx hW_sub hbij unfolding bij_betw_def by (by100 blast)
          ultimately show "y \<in> {y \<in> R2_0. inv_into ?X h y \<in> W}" using hx(1) by (by100 blast)
        qed
        \<comment> \<open>h ` W is open: h = t \<circ> \<sigma>, \<sigma> maps open to open, t maps open to open.\<close>
        have "\<sigma> ` W \<in> TR2_q'"
        proof -
          \<comment> \<open>\<sigma>\<inverse> continuous: {x \<in> X. \<sigma> x \<in> V} = {x \<in> X. x \<in> \<sigma>\<inverse>(V)} for V open.
             Since \<sigma> bijective: \<sigma> ` W = {v \<in> R2_q'. \<sigma>\<inverse>(v) \<in> W} = preimage of W under \<sigma>\<inverse>.\<close>
          have hinv_\<sigma>_cont: "top1_continuous_map_on R2_q' TR2_q' ?X ?TX (inv_into ?X \<sigma>)"
            using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
          have hbij_\<sigma>: "bij_betw \<sigma> ?X R2_q'"
            using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
          have "\<sigma> ` W = {v \<in> R2_q'. inv_into ?X \<sigma> v \<in> W}"
          proof (rule set_eqI, rule iffI)
            fix v assume "v \<in> \<sigma> ` W"
            then obtain x where "x \<in> W" "v = \<sigma> x" by (by100 blast)
            have "x \<in> ?X" using \<open>x \<in> W\<close> hW_sub by (by100 blast)
            hence "inv_into ?X \<sigma> v = x"
              using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij_\<sigma>] \<open>x \<in> ?X\<close>] \<open>v = \<sigma> x\<close> by (by100 simp)
            moreover have "v \<in> R2_q'" using \<open>x \<in> ?X\<close> hbij_\<sigma> \<open>v = \<sigma> x\<close> unfolding bij_betw_def by (by100 blast)
            ultimately show "v \<in> {v \<in> R2_q'. inv_into ?X \<sigma> v \<in> W}" using \<open>x \<in> W\<close> by (by100 blast)
          next
            fix v assume "v \<in> {v \<in> R2_q'. inv_into ?X \<sigma> v \<in> W}"
            hence "v \<in> R2_q'" "inv_into ?X \<sigma> v \<in> W" by (by100 auto)
            have "v \<in> \<sigma> ` ?X" using \<open>v \<in> R2_q'\<close> hbij_\<sigma> unfolding bij_betw_def by (by100 blast)
            have "v = \<sigma> (inv_into ?X \<sigma> v)" using f_inv_into_f[OF \<open>v \<in> \<sigma> ` ?X\<close>] by (by100 simp)
            thus "v \<in> \<sigma> ` W" using \<open>inv_into ?X \<sigma> v \<in> W\<close> by (by100 blast)
          qed
          moreover have "{v \<in> R2_q'. inv_into ?X \<sigma> v \<in> W} \<in> TR2_q'"
            using hinv_\<sigma>_cont \<open>W \<in> ?TX\<close> unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have "t ` (\<sigma> ` W) \<in> TR2_0"
        proof -
          have hinv_t_cont: "top1_continuous_map_on R2_0 TR2_0 R2_q' TR2_q' (inv_into R2_q' t)"
            using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hbij_t: "bij_betw t R2_q' R2_0"
            using ht_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hsW_sub: "\<sigma> ` W \<subseteq> R2_q'"
          proof -
            have "\<sigma> ` W \<subseteq> \<sigma> ` ?X" using hW_sub by (by100 blast)
            moreover have "bij_betw \<sigma> ?X R2_q'"
              using h\<sigma>_restrict unfolding top1_homeomorphism_on_def by (by100 blast)
            ultimately show ?thesis using bij_betw_imp_surj_on by (by100 fast)
          qed
          have "t ` (\<sigma> ` W) = {v \<in> R2_0. inv_into R2_q' t v \<in> \<sigma> ` W}"
          proof (rule set_eqI, rule iffI)
            fix v assume "v \<in> t ` (\<sigma> ` W)"
            then obtain u where "u \<in> \<sigma> ` W" "v = t u" by (by100 blast)
            have "u \<in> R2_q'" using \<open>u \<in> \<sigma> ` W\<close> hsW_sub by (by100 blast)
            hence "inv_into R2_q' t v = u"
              using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij_t] \<open>u \<in> R2_q'\<close>] \<open>v = t u\<close> by (by100 simp)
            moreover have "v \<in> R2_0" using \<open>u \<in> R2_q'\<close> hbij_t \<open>v = t u\<close> unfolding bij_betw_def by (by100 blast)
            ultimately show "v \<in> {v \<in> R2_0. inv_into R2_q' t v \<in> \<sigma> ` W}" using \<open>u \<in> \<sigma> ` W\<close> by (by100 blast)
          next
            fix v assume "v \<in> {v \<in> R2_0. inv_into R2_q' t v \<in> \<sigma> ` W}"
            hence "v \<in> R2_0" "inv_into R2_q' t v \<in> \<sigma> ` W" by (by100 auto)
            have "v \<in> t ` R2_q'" using \<open>v \<in> R2_0\<close> hbij_t unfolding bij_betw_def by (by100 blast)
            have "v = t (inv_into R2_q' t v)" using f_inv_into_f[OF \<open>v \<in> t ` R2_q'\<close>] by (by100 simp)
            thus "v \<in> t ` (\<sigma> ` W)" using \<open>inv_into R2_q' t v \<in> \<sigma> ` W\<close> by (by100 blast)
          qed
          moreover have "{v \<in> R2_0. inv_into R2_q' t v \<in> \<sigma> ` W} \<in> TR2_0"
            using hinv_t_cont \<open>\<sigma> ` W \<in> TR2_q'\<close> unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have "h ` W = t ` (\<sigma> ` W)" unfolding h_def by (by100 auto)
        show "{y \<in> R2_0. inv_into ?X h y \<in> W} \<in> TR2_0"
          unfolding heq \<open>h ` W = t ` (\<sigma> ` W)\<close> by (rule \<open>t ` (\<sigma> ` W) \<in> TR2_0\<close>)
      qed
    qed
  qed
  \<comment> \<open>Step 6: Homeomorphism \<Rightarrow> homotopy equivalence.\<close>
  have hh_htpeq: "top1_homotopy_equivalence_on ?X ?TX R2_0 TR2_0 h (inv_into ?X h)"
    unfolding top1_homotopy_equivalence_on_def
  proof (intro conjI)
    show "top1_continuous_map_on ?X ?TX R2_0 TR2_0 h"
      using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    show "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X h)"
      using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    \<comment> \<open>inv \<circ> h = id on X, h \<circ> inv = id on R2_0.\<close>
    \<comment> \<open>Both homotopies: inv\<circ>h = id on X and h\<circ>inv = id on R2_0.
       The constant homotopy H(x,t) = x works. This is the fst projection X\<times>I \<rightarrow> X.\<close>
    show "top1_homotopic_on ?X ?TX ?X ?TX (inv_into ?X h \<circ> h) (\<lambda>x. x)"
      unfolding top1_homotopic_on_def
    proof (intro conjI exI[of _ "\<lambda>(x,t). x"])
      have hh_cont: "top1_continuous_map_on ?X ?TX R2_0 TR2_0 h"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinv_cont: "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X h)"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      show "top1_continuous_map_on ?X ?TX ?X ?TX (inv_into ?X h \<circ> h)"
        by (rule top1_continuous_map_on_comp[OF hh_cont hinv_cont])
      show "top1_continuous_map_on ?X ?TX ?X ?TX (\<lambda>x. x)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> ?X" thus "x \<in> ?X" .
      next
        fix W assume "W \<in> ?TX"
        then obtain W0 where "W0 \<in> top1_S2_topology" "W = ?X \<inter> W0"
          unfolding subspace_topology_def by (by100 blast)
        hence "{x \<in> ?X. x \<in> W} = W" by (by100 blast)
        thus "{x \<in> ?X. x \<in> W} \<in> ?TX" using \<open>W \<in> ?TX\<close> by (by100 simp)
      qed
      show "top1_continuous_map_on (?X \<times> I_set) (product_topology_on ?TX I_top) ?X ?TX (\<lambda>(x, t). x)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume hp: "p \<in> ?X \<times> I_set"
        obtain x t where hxt: "p = (x, t)" "x \<in> ?X" "t \<in> I_set"
          using hp by (by100 blast)
        show "(case p of (x, t) \<Rightarrow> x) \<in> ?X" using hxt by (by100 simp)
      next
        fix W assume hW: "W \<in> ?TX"
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hI_mem: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by (by100 blast)
        \<comment> \<open>{p \<in> X\<times>I. fst p \<in> W} = W \<times> I_set (since W \<subseteq> X from subspace topology).\<close>
        have hW_sub: "W \<subseteq> ?X"
        proof -
          obtain W0 where "W = ?X \<inter> W0" using hW unfolding subspace_topology_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have "{p \<in> ?X \<times> I_set. (case p of (x, t) \<Rightarrow> x) \<in> W} = W \<times> I_set"
        proof (rule set_eqI, rule iffI)
          fix p assume hp: "p \<in> {p \<in> ?X \<times> I_set. (case p of (x, t) \<Rightarrow> x) \<in> W}"
          obtain x t where hxt: "p = (x,t)" "x \<in> ?X" "t \<in> I_set" "(case (x,t) of (x,t) \<Rightarrow> x) \<in> W"
            using hp by (by100 blast)
          have "x \<in> W" using hxt(4) by (by100 simp)
          thus "p \<in> W \<times> I_set" using hxt(1,3) by (by100 blast)
        next
          fix p assume hp: "p \<in> W \<times> I_set"
          obtain x t where "p = (x,t)" "x \<in> W" "t \<in> I_set" using hp by (by100 blast)
          hence "x \<in> ?X" using hW_sub by (by100 blast)
          show "p \<in> {p \<in> ?X \<times> I_set. (case p of (x, t) \<Rightarrow> x) \<in> W}"
            using \<open>p = (x,t)\<close> \<open>x \<in> W\<close> \<open>x \<in> ?X\<close> \<open>t \<in> I_set\<close> by (by100 simp)
        qed
        moreover have "W \<times> I_set \<in> product_topology_on ?TX I_top"
          by (rule product_rect_open[OF hW hI_mem])
        ultimately show "{p \<in> ?X \<times> I_set. (case p of (x, t) \<Rightarrow> x) \<in> W} \<in> product_topology_on ?TX I_top"
          by (by100 simp)
      qed
      show "\<forall>x\<in>?X. (case (x, 0::real) of (x, t) \<Rightarrow> x) = (inv_into ?X h \<circ> h) x"
      proof
        fix x assume hx: "x \<in> ?X"
        have hbij_h: "bij_betw h ?X R2_0"
          using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have "inv_into ?X h (h x) = x"
          using inv_into_f_f[OF bij_betw_imp_inj_on[OF hbij_h] hx] by (by100 simp)
        thus "(case (x, 0::real) of (x, t) \<Rightarrow> x) = (inv_into ?X h \<circ> h) x"
          unfolding comp_def by (by100 simp)
      qed
      show "\<forall>x\<in>?X. (case (x, 1::real) of (x, t) \<Rightarrow> x) = x" by (by100 simp)
    qed
    show "top1_homotopic_on R2_0 TR2_0 R2_0 TR2_0 (h \<circ> inv_into ?X h) (\<lambda>y. y)"
      unfolding top1_homotopic_on_def
    proof (intro conjI exI[of _ "\<lambda>(y,t). y"])
      have hh_cont: "top1_continuous_map_on ?X ?TX R2_0 TR2_0 h"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinv_cont: "top1_continuous_map_on R2_0 TR2_0 ?X ?TX (inv_into ?X h)"
        using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      show "top1_continuous_map_on R2_0 TR2_0 R2_0 TR2_0 (h \<circ> inv_into ?X h)"
        by (rule top1_continuous_map_on_comp[OF hinv_cont hh_cont])
      show "top1_continuous_map_on R2_0 TR2_0 R2_0 TR2_0 (\<lambda>y. y)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix y assume "y \<in> R2_0" thus "y \<in> R2_0" .
      next
        fix W assume "W \<in> TR2_0"
        have "W \<subseteq> R2_0"
        proof -
          obtain W0 where "W = R2_0 \<inter> W0"
            using \<open>W \<in> TR2_0\<close> unfolding TR2_0_def R2_0_def subspace_topology_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        hence "{y \<in> R2_0. y \<in> W} = W" by (by100 blast)
        thus "{y \<in> R2_0. y \<in> W} \<in> TR2_0" using \<open>W \<in> TR2_0\<close> by (by100 simp)
      qed
      show "top1_continuous_map_on (R2_0 \<times> I_set) (product_topology_on TR2_0 I_top) R2_0 TR2_0 (\<lambda>(y, t). y)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume hp: "p \<in> R2_0 \<times> I_set"
        obtain y t where "p = (y, t)" "y \<in> R2_0" using hp by (by100 blast)
        thus "(case p of (y, t) \<Rightarrow> y) \<in> R2_0" by (by100 simp)
      next
        fix W assume hW: "W \<in> TR2_0"
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hI_mem: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by (by100 blast)
        have hW_sub: "W \<subseteq> R2_0"
        proof -
          obtain W0 where "W = R2_0 \<inter> W0"
            using hW unfolding TR2_0_def R2_0_def subspace_topology_def by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have "{p \<in> R2_0 \<times> I_set. (case p of (y, t) \<Rightarrow> y) \<in> W} = W \<times> I_set"
        proof (rule set_eqI, rule iffI)
          fix p assume hp: "p \<in> {p \<in> R2_0 \<times> I_set. (case p of (y, t) \<Rightarrow> y) \<in> W}"
          obtain y t where hyt: "p = (y,t)" "y \<in> R2_0" "t \<in> I_set"
              "(case (y,t) of (y,t) \<Rightarrow> y) \<in> W"
            using hp by (by100 blast)
          have "y \<in> W" using hyt(4) by (by100 simp)
          thus "p \<in> W \<times> I_set" using hyt(1,3) by (by100 blast)
        next
          fix p assume hp: "p \<in> W \<times> I_set"
          obtain y t where "p = (y,t)" "y \<in> W" "t \<in> I_set" using hp by (by100 blast)
          hence "y \<in> R2_0" using hW_sub by (by100 blast)
          show "p \<in> {p \<in> R2_0 \<times> I_set. (case p of (y, t) \<Rightarrow> y) \<in> W}"
            using \<open>p = (y,t)\<close> \<open>y \<in> W\<close> \<open>y \<in> R2_0\<close> \<open>t \<in> I_set\<close> by (by100 simp)
        qed
        moreover have "W \<times> I_set \<in> product_topology_on TR2_0 I_top"
          by (rule product_rect_open[OF hW hI_mem])
        ultimately show "{p \<in> R2_0 \<times> I_set. (case p of (y, t) \<Rightarrow> y) \<in> W} \<in> product_topology_on TR2_0 I_top"
          by (by100 simp)
      qed
      show "\<forall>y\<in>R2_0. (case (y, 0::real) of (y, t) \<Rightarrow> y) = (h \<circ> inv_into ?X h) y"
      proof
        fix y assume hy: "y \<in> R2_0"
        have hbij_h: "bij_betw h ?X R2_0"
          using hh_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have "y \<in> h ` ?X" using hy hbij_h unfolding bij_betw_def by (by100 blast)
        have "h (inv_into ?X h y) = y" using f_inv_into_f[OF \<open>y \<in> h ` ?X\<close>] by (by100 simp)
        thus "(case (y, 0::real) of (y, t) \<Rightarrow> y) = (h \<circ> inv_into ?X h) y"
          unfolding comp_def by (by100 simp)
      qed
      show "\<forall>y\<in>R2_0. (case (y, 1::real) of (y, t) \<Rightarrow> y) = y" by (by100 simp)
    qed
  qed
  have ha_X: "a \<in> ?X" using assms(5) by (by100 blast)
  have hpi1_iso_R2: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?X ?TX a)
      (top1_fundamental_group_mul ?X ?TX a)
      (top1_fundamental_group_carrier R2_0 TR2_0 (h a))
      (top1_fundamental_group_mul R2_0 TR2_0 (h a))"
    using Theorem_58_7[OF hTX hTR2_0 hh_htpeq ha_X] by (by100 blast)
  \<comment> \<open>Step 7: Chain with Theorem_58_2 (R^2-{0} \<cong> S^1) and Theorem_54_5 (\<pi>_1(S^1) \<cong> Z).
     This gives \<pi>_1(X, a) \<cong> Z.\<close>
  \<comment> \<open>Step 8: Extract generator from Z-isomorphism.\<close>
  \<comment> \<open>Step 7-8: From \<pi>_1(X,a) \<cong> Z, extract generator.\<close>
  \<comment> \<open>The chain \<pi>_1(X,a) \<cong> \<pi>_1(R^2-{0}, h(a)) \<cong> \<pi>_1(S^1, (1,0)) \<cong> Z
     gives a group isomorphism \<phi>: \<pi>_1(X,a) \<rightarrow> Z.
     Let gen_class = \<phi>\<inverse>(1). Pick a representative gen from gen_class.
     For any loop f: \<phi>([f]) = n. [f] = [gen]^n in the group.
     For n \<ge> 0: f \<simeq> gen^n (path_power). For n < 0: f \<simeq> (gen\<inverse>)^{|n|}.\<close>
  \<comment> \<open>From hpi1_iso_R2 + Theorem_58_2 + Theorem_54_5: \<pi>_1(X,a) \<cong> Z.\<close>
  have hpi1_iso_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier ?X ?TX a)
      (top1_fundamental_group_mul ?X ?TX a)
      top1_Z_group top1_Z_mul"
  proof -
    \<comment> \<open>Step 1: \<pi>_1(R^2-{0}, h(a)) \<cong> \<pi>_1(R^2-{0}, (1,0)) via basepoint change.\<close>
    have hR2_0_pc: "top1_path_connected_on R2_0 TR2_0"
      unfolding R2_0_def TR2_0_def using R2_minus_point_path_connected[of "(0,0)"] by (by100 simp)
    have hha_R2: "h a \<in> R2_0"
    proof -
      have "a \<in> ?X" using ha_X .
      hence "\<sigma> a \<in> R2_q'"
        using h\<sigma>_restrict unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      hence "t (\<sigma> a) \<in> R2_0"
        using ht_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      thus ?thesis unfolding h_def comp_def by (by100 simp)
    qed
    have h10_R2: "(1::real, 0::real) \<in> R2_0" unfolding R2_0_def by (by100 simp)
    have hbp_change: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier R2_0 TR2_0 (h a))
        (top1_fundamental_group_mul R2_0 TR2_0 (h a))
        (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
      by (rule Theorem_52_1_iso[OF hTR2_0 hR2_0_pc hha_R2 h10_R2])
    \<comment> \<open>Step 2: \<pi>_1(S^1, (1,0)) \<cong> \<pi>_1(R^2-{0}, (1,0)) (Theorem_58_2 with matching TR2_0).\<close>
    have hTR2_0_eq: "TR2_0 = subspace_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
      unfolding TR2_0_def R2_0_def by (by100 simp)
    have hR2_0_eq: "R2_0 = UNIV - {(0::real, 0::real)}" unfolding R2_0_def by (by100 simp)
    have h58_2: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1
          (subspace_topology (UNIV - {(0::real, 0::real)})
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
              (UNIV - {(0, 0)})) top1_S1) (1, 0))
        (top1_fundamental_group_mul top1_S1
          (subspace_topology (UNIV - {(0::real, 0::real)})
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
              (UNIV - {(0, 0)})) top1_S1) (1, 0))
        (top1_fundamental_group_carrier (UNIV - {(0::real, 0::real)})
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - {(0, 0)})) (1, 0))
        (top1_fundamental_group_mul (UNIV - {(0::real, 0::real)})
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - {(0, 0)})) (1, 0))"
      by (rule Theorem_58_2_inclusion_iso)
    \<comment> \<open>Step 3: Match S^1 topologies. subspace R2_0 TR2_0 S^1 = top1_S1_topology.\<close>
    have hS1_top_eq: "subspace_topology R2_0 TR2_0 top1_S1 = top1_S1_topology"
    proof -
      have hS1_sub: "top1_S1 \<subseteq> R2_0" unfolding R2_0_def top1_S1_def by (by100 auto)
      \<comment> \<open>Direct proof: both sides equal {S^1 \<inter> W | W \<in> product_topology_on ...}.\<close>
      show ?thesis
      proof (rule set_eqI, rule iffI)
        fix W assume "W \<in> subspace_topology R2_0 TR2_0 top1_S1"
        then obtain V where hV: "V \<in> TR2_0" "W = top1_S1 \<inter> V"
          unfolding subspace_topology_def by (by100 blast)
        then obtain V0 where hV0: "V0 \<in> product_topology_on top1_open_sets top1_open_sets"
            "V = R2_0 \<inter> V0" unfolding TR2_0_def R2_0_def subspace_topology_def by (by100 blast)
        have "W = top1_S1 \<inter> V0" using hV(2) hV0(2) hS1_sub by (by100 blast)
        thus "W \<in> top1_S1_topology" unfolding top1_S1_topology_def subspace_topology_def
          using hV0(1) by (by100 blast)
      next
        fix W assume "W \<in> top1_S1_topology"
        then obtain V0 where hV0: "V0 \<in> product_topology_on top1_open_sets top1_open_sets"
            "W = top1_S1 \<inter> V0" unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
        have "R2_0 \<inter> V0 \<in> TR2_0" unfolding TR2_0_def R2_0_def subspace_topology_def
          using hV0(1) by (by100 blast)
        moreover have "W = top1_S1 \<inter> (R2_0 \<inter> V0)" using hV0(2) hS1_sub by (by100 blast)
        ultimately show "W \<in> subspace_topology R2_0 TR2_0 top1_S1"
          unfolding subspace_topology_def by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 4: \<pi>_1(S^1, (1,0)) \<cong> Z (Theorem_54_5_iso).\<close>
    have h54_5: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        top1_Z_group top1_Z_mul"
      by (rule Theorem_54_5_iso)
    \<comment> \<open>Step 5: Compose the chain. Need transitivity of groups_isomorphic_on.\<close>
    \<comment> \<open>Compose: need transitivity + symmetry of groups_isomorphic_on.
       groups_isomorphic_on G mulG H mulH \<equiv> \<exists>f. group_iso_on G mulG H mulH f
       group_iso_on \<equiv> group_hom_on + bij_betw.
       Transitivity: compose hom + bij. Symmetry: inverse.\<close>
    \<comment> \<open>Rewrite h58_2 using hS1_top_eq to match S^1 topologies.\<close>
    have h58_2': "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0))
        (top1_fundamental_group_mul R2_0 TR2_0 (1, 0))"
      using h58_2 hS1_top_eq hR2_0_eq hTR2_0_eq by (by100 simp)
    \<comment> \<open>Chain: compose 4 group isos. Use transitivity + symmetry.\<close>
    show ?thesis unfolding top1_groups_isomorphic_on_def
    proof -
      \<comment> \<open>Extract individual isomorphisms.\<close>
      obtain f1 where hf1: "top1_group_iso_on
          (top1_fundamental_group_carrier ?X ?TX a) (top1_fundamental_group_mul ?X ?TX a)
          (top1_fundamental_group_carrier R2_0 TR2_0 (h a)) (top1_fundamental_group_mul R2_0 TR2_0 (h a)) f1"
        using hpi1_iso_R2 unfolding top1_groups_isomorphic_on_def by (by100 blast)
      obtain f2 where hf2: "top1_group_iso_on
          (top1_fundamental_group_carrier R2_0 TR2_0 (h a)) (top1_fundamental_group_mul R2_0 TR2_0 (h a))
          (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0)) (top1_fundamental_group_mul R2_0 TR2_0 (1, 0)) f2"
        using hbp_change unfolding top1_groups_isomorphic_on_def by (by100 blast)
      obtain f3 where hf3: "top1_group_iso_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
          (top1_fundamental_group_carrier R2_0 TR2_0 (1, 0)) (top1_fundamental_group_mul R2_0 TR2_0 (1, 0)) f3"
        using h58_2' unfolding top1_groups_isomorphic_on_def by (by100 blast)
      obtain f4 where hf4: "top1_group_iso_on
          (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
          top1_Z_group top1_Z_mul f4"
        using h54_5 unfolding top1_groups_isomorphic_on_def by (by100 blast)
      \<comment> \<open>Compose: f4 \<circ> inv(f3) \<circ> f2 \<circ> f1 : \<pi>_1(X) \<rightarrow> Z.\<close>
      define \<psi> where "\<psi> = f4 \<circ> inv_into G4 f3 \<circ> f2 \<circ> f1"
      \<comment> \<open>Show \<psi> is a group iso by composing hom + bij.\<close>
      define G1 where "G1 = top1_fundamental_group_carrier ?X ?TX a"
      define M1 where "M1 = top1_fundamental_group_mul ?X ?TX a"
      define G2 where "G2 = top1_fundamental_group_carrier R2_0 TR2_0 (h a)"
      define M2 where "M2 = top1_fundamental_group_mul R2_0 TR2_0 (h a)"
      define G3 where "G3 = top1_fundamental_group_carrier R2_0 TR2_0 (1, 0)"
      define M3 where "M3 = top1_fundamental_group_mul R2_0 TR2_0 (1, 0)"
      define G4 where "G4 = top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
      define M4 where "M4 = top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0)"
      have hf1': "top1_group_iso_on G1 M1 G2 M2 f1"
        using hf1 unfolding G1_def M1_def G2_def M2_def .
      have hf2': "top1_group_iso_on G2 M2 G3 M3 f2"
        using hf2 unfolding G2_def M2_def G3_def M3_def .
      have hf3': "top1_group_iso_on G4 M4 G3 M3 f3"
        using hf3 unfolding G4_def M4_def G3_def M3_def .
      have hf4': "top1_group_iso_on G4 M4 top1_Z_group top1_Z_mul f4"
        using hf4 unfolding G4_def M4_def .
      \<comment> \<open>Bijections.\<close>
      have hb1: "bij_betw f1 G1 G2" using hf1' unfolding top1_group_iso_on_def by (by100 blast)
      have hb2: "bij_betw f2 G2 G3" using hf2' unfolding top1_group_iso_on_def by (by100 blast)
      have hb3: "bij_betw f3 G4 G3" using hf3' unfolding top1_group_iso_on_def by (by100 blast)
      have hb3i: "bij_betw (inv_into G4 f3) G3 G4"
        by (rule bij_betw_inv_into[OF hb3])
      have hb4: "bij_betw f4 G4 top1_Z_group" using hf4' unfolding top1_group_iso_on_def by (by100 blast)
      \<comment> \<open>Compose bijections.\<close>
      \<comment> \<open>Build bij_betw for \<psi> directly.\<close>
      \<comment> \<open>Prove \<psi> is a group iso: bij_betw + group_hom_on.\<close>
      \<comment> \<open>\<psi> is a group iso: compose 4 individual group isos.\<close>
      have h\<psi>_iso: "top1_group_iso_on G1 M1 top1_Z_group top1_Z_mul \<psi>"
        sorry \<comment> \<open>\<psi> = f4 \<circ> f3\<inverse> \<circ> f2 \<circ> f1. Each is a group iso (hf1'-hf4', hb1-hb4, hb3i).
           bij_betw: bij_betw_trans chain. group_hom_on: compose hom preserving mul.
           The proof is purely mechanical group theory but requires careful handling of
           by100 limits with the composition normalization.\<close>
      have h\<psi>_bij: "bij_betw \<psi> G1 top1_Z_group"
        using h\<psi>_iso unfolding top1_group_iso_on_def by (by100 blast)
      have h\<psi>_hom: "top1_group_hom_on G1 M1 top1_Z_group top1_Z_mul \<psi>"
        using h\<psi>_iso unfolding top1_group_iso_on_def by (by100 blast)
      show "\<exists>f. top1_group_iso_on G1 M1 top1_Z_group top1_Z_mul f"
        using h\<psi>_bij h\<psi>_hom unfolding G1_def M1_def top1_group_iso_on_def by (by100 blast)
    qed
  qed
  \<comment> \<open>Extract generator from Z-isomorphism.\<close>
  show ?thesis
    sorry \<comment> \<open>From hpi1_iso_Z: \<exists>\<psi> bijective homomorphism \<pi>_1(X,a) \<rightarrow> Z.
       Let gen_class = \<psi>\<inverse>(1). Pick gen \<in> gen_class (a loop at a).
       For any loop f: \<psi>([f]) = n. Since \<psi> is homomorphism:
         \<psi>([gen]^n) = n\<cdot>\<psi>([gen]) = n\<cdot>1 = n (by group hom + induction).
       Bijectivity: [f] = [gen]^n = [gen^n] (by fund. group mul = path product).
       For n\<ge>0: f \<simeq> gen^n (same homotopy class). For n<0: f \<simeq> (gen\<inverse>)^{|n|}.
       Proof requires: group iso extraction (\<exists>-elim), representative extraction
       from homotopy class (Hilbert choice), n-fold group product = path_power class
       (induction on n using top1_fundamental_group_mul_def), homotopy class membership
       = path homotopy (by top1_loop_equiv_on_def). Each step is ~10-20 lines.\<close>
qed

text \<open>If f \<simeq> g (loops at a), then f^n \<simeq> g^n.\<close>
lemma path_homotopic_path_power:
  assumes "is_topology_on X TX"
      and "top1_path_homotopic_on X TX a a f g"
      and "top1_is_path_on X TX a a f" and "top1_is_path_on X TX a a g"
  shows "top1_path_homotopic_on X TX a a (top1_path_power f a n) (top1_path_power g a n)"
proof (induction n)
  case 0
  have haX: "a \<in> X"
  proof -
    have "f 0 = a" using assms(3) unfolding top1_is_path_on_def by (by100 blast)
    moreover have "f 0 \<in> X"
    proof -
      have "\<forall>s\<in>I_set. f s \<in> X" using assms(3)
        unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately show ?thesis by simp
  qed
  show ?case by (simp add: Lemma_51_1_path_homotopic_refl[OF
      top1_constant_path_is_path[OF assms(1) haX]])
next
  case (Suc n)
  \<comment> \<open>f^{n+1} = f * f^n \<simeq> g * g^n = g^{n+1} by product compatibility.\<close>
  have hfn: "top1_is_path_on X TX a a (top1_path_power f a n)"
    by (rule top1_path_power_is_path[OF assms(1)]) (simp add: assms(3) top1_is_loop_on_def)
  have hgn: "top1_is_path_on X TX a a (top1_path_power g a n)"
    by (rule top1_path_power_is_path[OF assms(1)]) (simp add: assms(4) top1_is_loop_on_def)
  have h1: "top1_path_homotopic_on X TX a a (top1_path_product f (top1_path_power f a n))
      (top1_path_product g (top1_path_power f a n))"
    by (rule path_homotopic_product_left[OF assms(1) assms(2) hfn])
  have h2: "top1_path_homotopic_on X TX a a (top1_path_product g (top1_path_power f a n))
      (top1_path_product g (top1_path_power g a n))"
    by (rule path_homotopic_product_right[OF assms(1) Suc assms(4)])
  show ?case by (simp add: Lemma_51_1_path_homotopic_trans[OF assms(1) h1 h2])
qed


text \<open>Path power addition: f^a * f^b \<simeq> f^{a+b} (for loops at a).\<close>
lemma path_power_product_add:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_path_homotopic_on X TX a a
    (top1_path_product (top1_path_power f a m) (top1_path_power f a n))
    (top1_path_power f a (m + n))"
proof (induction m)
  case 0
  \<comment> \<open>const * f^n \<simeq> f^n = f^{0+n}.\<close>
  show ?case by (simp add: Theorem_51_2_left_identity[OF assms(1)
      top1_path_power_is_path[OF assms]])
next
  case (Suc m)
  \<comment> \<open>f^{m+1} * f^n = (f * f^m) * f^n \<simeq> f * (f^m * f^n) \<simeq> f * f^{m+n} = f^{m+1+n}.\<close>
  have hf: "top1_is_path_on X TX a a f" using assms(2) unfolding top1_is_loop_on_def by simp
  have hfm: "top1_is_path_on X TX a a (top1_path_power f a m)"
    by (rule top1_path_power_is_path[OF assms])
  have hfn: "top1_is_path_on X TX a a (top1_path_power f a n)"
    by (rule top1_path_power_is_path[OF assms])
  have hfmn: "top1_is_path_on X TX a a (top1_path_power f a (m + n))"
    by (rule top1_path_power_is_path[OF assms])
  have hfm_fn: "top1_is_path_on X TX a a (top1_path_product (top1_path_power f a m) (top1_path_power f a n))"
    by (rule top1_path_product_is_path[OF assms(1) hfm hfn])
  \<comment> \<open>Step 1: (f * f^m) * f^n \<simeq> f * (f^m * f^n) by associativity.\<close>
  have h_assoc: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_product f (top1_path_power f a m)) (top1_path_power f a n))
      (top1_path_product f (top1_path_product (top1_path_power f a m) (top1_path_power f a n)))"
    by (rule Lemma_51_1_path_homotopic_sym[OF
        Theorem_51_2_associativity[OF assms(1) hf hfm hfn]])
  \<comment> \<open>Step 2: f * (f^m * f^n) \<simeq> f * f^{m+n} by IH.\<close>
  have h_IH: "top1_path_homotopic_on X TX a a
      (top1_path_product f (top1_path_product (top1_path_power f a m) (top1_path_power f a n)))
      (top1_path_product f (top1_path_power f a (m + n)))"
    by (rule path_homotopic_product_right[OF assms(1) Suc hf])
  \<comment> \<open>Combine.\<close>
  have "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a (Suc m)) (top1_path_power f a n))
      (top1_path_product f (top1_path_product (top1_path_power f a m) (top1_path_power f a n)))"
    using h_assoc by simp
  hence "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a (Suc m)) (top1_path_power f a n))
      (top1_path_product f (top1_path_power f a (m + n)))"
    by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) _ h_IH])
  thus ?case by simp
qed

text \<open>Path power multiplication: (f^m)^n \<simeq> f^{m*n} (for loops at a).\<close>
lemma path_power_mult:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_path_homotopic_on X TX a a
    (top1_path_power (top1_path_power f a m) a n)
    (top1_path_power f a (m * n))"
proof (induction n)
  case 0
  have haX: "a \<in> X"
    using top1_is_loop_on_start[OF assms(2)]
          top1_is_loop_on_continuous[OF assms(2)]
    unfolding top1_continuous_map_on_def top1_unit_interval_def by force
  show ?case by (simp add: Lemma_51_1_path_homotopic_refl[OF
      top1_constant_path_is_path[OF assms(1) haX]])
next
  case (Suc n)
  have hfm_loop: "top1_is_loop_on X TX a (top1_path_power f a m)"
    by (rule top1_path_power_is_loop[OF assms])
  have hfm: "top1_is_path_on X TX a a (top1_path_power f a m)"
    using hfm_loop unfolding top1_is_loop_on_def by simp
  have h1: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a m) (top1_path_power (top1_path_power f a m) a n))
      (top1_path_product (top1_path_power f a m) (top1_path_power f a (m * n)))"
    by (rule path_homotopic_product_right[OF assms(1) Suc hfm])
  have h2: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a m) (top1_path_power f a (m * n)))
      (top1_path_power f a (m + m * n))"
    by (rule path_power_product_add[OF assms])
  have h12: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power f a m) (top1_path_power (top1_path_power f a m) a n))
      (top1_path_power f a (m + m * n))"
    by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) h1 h2])
  have hgoal_lhs: "top1_path_power (top1_path_power f a m) a (Suc n)
      = top1_path_product (top1_path_power f a m) (top1_path_power (top1_path_power f a m) a n)"
    by simp
  have hgoal_rhs: "m * Suc n = m + m * n" by simp
  show ?case using h12 unfolding hgoal_lhs hgoal_rhs .
qed


text \<open>Reverse distributes over power: (f^n)\<inverse> \<simeq> (f\<inverse>)^n.\<close>
lemma path_power_reverse:
  assumes "is_topology_on X TX" and "top1_is_loop_on X TX a f"
  shows "top1_path_homotopic_on X TX a a
    (top1_path_reverse (top1_path_power f a n))
    (top1_path_power (top1_path_reverse f) a n)"
proof (induction n)
  case 0
  \<comment> \<open>(const)\<inverse> = const = (f\<inverse>)^0. Definitional.\<close>
  have haX: "a \<in> X"
    using top1_is_loop_on_start[OF assms(2)] top1_is_loop_on_continuous[OF assms(2)]
    unfolding top1_continuous_map_on_def top1_unit_interval_def by force
  have "top1_path_reverse (top1_constant_path a) = top1_constant_path a"
    unfolding top1_path_reverse_def top1_constant_path_def by auto
  thus ?case by (simp add: Lemma_51_1_path_homotopic_refl[OF
      top1_constant_path_is_path[OF assms(1) haX]])
next
  case (Suc n)
  \<comment> \<open>(f * f^n)\<inverse> = (f^n)\<inverse> * f\<inverse> (definitional).
     \<simeq> (f\<inverse>)^n * f\<inverse> (IH + product left).
     \<simeq> (f\<inverse>)^n * (f\<inverse>)^1 (product right with f\<inverse> \<simeq> (f\<inverse>)^1 via right identity sym).
     \<simeq> (f\<inverse>)^{n+1} (path_power_product_add).\<close>
  have hf: "top1_is_path_on X TX a a f" using assms(2) unfolding top1_is_loop_on_def by simp
  have hfr: "top1_is_path_on X TX a a (top1_path_reverse f)"
    using top1_path_reverse_is_path[OF hf] hf unfolding top1_is_path_on_def top1_path_reverse_def by auto
  have hfr_loop: "top1_is_loop_on X TX a (top1_path_reverse f)"
    by (rule top1_path_reverse_is_loop[OF assms(2)])
  have hfn: "top1_is_path_on X TX a a (top1_path_power f a n)"
    by (rule top1_path_power_is_path[OF assms])
  have hfn_rev: "top1_is_path_on X TX a a (top1_path_reverse (top1_path_power f a n))"
    using top1_path_reverse_is_path[OF hfn] hfn
    unfolding top1_is_path_on_def top1_path_reverse_def by auto
  have hfrn: "top1_is_path_on X TX a a (top1_path_power (top1_path_reverse f) a n)"
    by (rule top1_path_power_is_path[OF assms(1) hfr_loop])
  \<comment> \<open>Step 1: (f * f^n)\<inverse> = (f^n)\<inverse> * f\<inverse> (definitional equality).\<close>
  have hrev_eq: "top1_path_reverse (top1_path_power f a (Suc n))
      = top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f)"
  proof (rule ext)
    fix s :: real
    have hf0: "f 0 = a" and hf1: "f 1 = a"
      using hf unfolding top1_is_path_on_def by (by100 blast)+
    have hfn0: "top1_path_power f a n 0 = a" and hfn1: "top1_path_power f a n 1 = a"
      using hfn unfolding top1_is_path_on_def by (by100 blast)+
    show "top1_path_reverse (top1_path_power f a (Suc n)) s
        = top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) s"
    proof (cases "s < 1/2")
      case True
      \<comment> \<open>s < 1/2, so 1-s > 1/2. LHS uses else branch, RHS uses then branch.\<close>
      have h1s: "\<not> ((1::real) - s \<le> 1/2)" using True by linarith
      have lhs: "top1_path_reverse (top1_path_power f a (Suc n)) s
          = top1_path_power f a n (1 - 2*s)"
      proof -
        have "top1_path_reverse (top1_path_power f a (Suc n)) s
            = top1_path_product f (top1_path_power f a n) (1 - s)"
          unfolding top1_path_reverse_def by simp
        also have "... = top1_path_power f a n (2 * (1 - s) - 1)"
          unfolding top1_path_product_def using h1s by simp
        also have "(2::real) * (1 - s) - 1 = 1 - 2 * s" by (simp add: algebra_simps)
        finally show ?thesis by simp
      qed
      have hs2: "s \<le> 1/2" using True by simp
      have rhs: "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) s
          = top1_path_power f a n (1 - 2*s)"
        unfolding top1_path_product_def top1_path_reverse_def using hs2 by simp
      show ?thesis using lhs rhs by simp
    next
      case False
      hence hs_ge: "s \<ge> 1/2" by simp
      show ?thesis
      proof (cases "s > 1/2")
        case True
        have h1s: "((1::real) - s) \<le> 1/2" using True by linarith
        have lhs: "top1_path_reverse (top1_path_power f a (Suc n)) s
            = f (2 - 2*s)"
        proof -
          have "top1_path_reverse (top1_path_power f a (Suc n)) s
              = top1_path_product f (top1_path_power f a n) (1 - s)"
            unfolding top1_path_reverse_def by simp
          also have "... = f (2 * (1 - s))"
            unfolding top1_path_product_def using h1s by simp
          also have "(2::real) * (1 - s) = 2 - 2 * s" by (simp add: algebra_simps)
          finally show ?thesis by simp
        qed
        have hs2: "\<not> (s \<le> 1/2)" using True by simp
        have rhs: "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) s
            = f (2 - 2*s)"
          unfolding top1_path_product_def top1_path_reverse_def using hs2 by simp
        show ?thesis using lhs rhs by simp
      next
        case False
        hence hs_eq: "s = 1/2" using hs_ge by simp
        \<comment> \<open>At s = 1/2: both sides = a (boundary between branches).\<close>
        have lhs': "top1_path_reverse (top1_path_power f a (Suc n)) (1/2) = a"
        proof -
          have "top1_path_reverse (top1_path_power f a (Suc n)) (1/2)
              = top1_path_product f (top1_path_power f a n) (1/2)"
            unfolding top1_path_reverse_def by simp
          also have "... = f (2 * (1/2))"
            unfolding top1_path_product_def by simp
          also have "... = f 1" by simp
          also have "... = a" using hf1 by simp
          finally show ?thesis .
        qed
        have rhs: "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) (1/2)
            = top1_path_power f a n (1 - 2 * (1/2))"
          unfolding top1_path_product_def top1_path_reverse_def by simp
        hence rhs': "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) (1/2) = a"
          using hfn0 by simp
        have hs12: "s = 1/2" using hs_eq by linarith
        have "top1_path_reverse (top1_path_power f a (Suc n)) s = a"
          by (subst hs12, rule lhs')
        moreover have "top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f) s = a"
          by (subst hs12, rule rhs')
        ultimately show ?thesis by simp
      qed
    qed
  qed
  \<comment> \<open>Step 2: (f^n)\<inverse> * f\<inverse> \<simeq> (f\<inverse>)^n * f\<inverse> (IH + product_left).\<close>
  have h2: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f))
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_reverse f))"
    by (rule path_homotopic_product_left[OF assms(1) Suc hfr])
  \<comment> \<open>Step 3: (f\<inverse>)^n * f\<inverse> \<simeq> (f\<inverse>)^n * (f\<inverse>)^1 (right identity sym: f\<inverse> \<simeq> f\<inverse> * const = (f\<inverse>)^1).\<close>
  have hfr_eq_fr1: "top1_path_homotopic_on X TX a a
      (top1_path_reverse f) (top1_path_power (top1_path_reverse f) a 1)"
  proof -
    have "(top1_path_power (top1_path_reverse f) a 1) =
        top1_path_product (top1_path_reverse f) (top1_constant_path a)" by simp
    moreover have "top1_path_homotopic_on X TX a a
        (top1_path_product (top1_path_reverse f) (top1_constant_path a)) (top1_path_reverse f)"
      by (rule Theorem_51_2_right_identity[OF assms(1) hfr])
    ultimately show ?thesis using Lemma_51_1_path_homotopic_sym by simp
  qed
  have h3: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_reverse f))
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_power (top1_path_reverse f) a 1))"
    by (rule path_homotopic_product_right[OF assms(1) hfr_eq_fr1 hfrn])
  \<comment> \<open>Step 4: (f\<inverse>)^n * (f\<inverse>)^1 \<simeq> (f\<inverse>)^{n+1} (path_power_product_add).\<close>
  have h4: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_power (top1_path_reverse f) a 1))
      (top1_path_power (top1_path_reverse f) a (n + 1))"
    by (rule path_power_product_add[OF assms(1) hfr_loop])
  \<comment> \<open>Chain: rev(f^{n+1}) = rev(f^n) * rev(f) \<simeq> (f\<inverse>)^n * f\<inverse> \<simeq> (f\<inverse>)^n * (f\<inverse>)^1 \<simeq> (f\<inverse>)^{n+1}.\<close>
  have h23: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f))
      (top1_path_product (top1_path_power (top1_path_reverse f) a n) (top1_path_power (top1_path_reverse f) a 1))"
    by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) h2 h3])
  have h234: "top1_path_homotopic_on X TX a a
      (top1_path_product (top1_path_reverse (top1_path_power f a n)) (top1_path_reverse f))
      (top1_path_power (top1_path_reverse f) a (n + 1))"
    by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) h23 h4])
  show ?case using h234 unfolding hrev_eq by simp
qed

text \<open>Corollary: if f \<simeq> g, then f\<inverse> \<simeq> g\<inverse>.\<close>
lemma path_homotopic_reverse:
  assumes "is_topology_on X TX"
      and "top1_path_homotopic_on X TX a a f g"
      and "top1_is_path_on X TX a a f" and "top1_is_path_on X TX a a g"
  shows "top1_path_homotopic_on X TX a a (top1_path_reverse f) (top1_path_reverse g)"
proof -
  \<comment> \<open>If F is a homotopy from f to g, then G(s,t) = F(1-s,t) is a homotopy from f\<inverse> to g\<inverse>.\<close>
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFl: "\<forall>t\<in>I_set. F (0, t) = a" and hFr: "\<forall>t\<in>I_set. F (1, t) = a"
    using assms(2) unfolding top1_path_homotopic_on_def by blast
  define G where "G = (\<lambda>(s::real, t::real). F (1 - s, t))"
  have hrf: "top1_is_path_on X TX a a (top1_path_reverse f)"
    using top1_path_reverse_is_path[OF assms(3)] unfolding top1_path_reverse_def
    using assms(3) unfolding top1_is_path_on_def by auto
  have hrg: "top1_is_path_on X TX a a (top1_path_reverse g)"
    using top1_path_reverse_is_path[OF assms(4)] unfolding top1_path_reverse_def
    using assms(4) unfolding top1_is_path_on_def by auto
  show ?thesis unfolding top1_path_homotopic_on_def
  proof (intro exI[of _ G] conjI)
    show "top1_is_path_on X TX a a (top1_path_reverse f)" by (rule hrf)
    show "top1_is_path_on X TX a a (top1_path_reverse g)" by (rule hrg)
    show "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX G"
    proof -
      define \<phi> :: "real \<times> real \<Rightarrow> real \<times> real" where "\<phi> = (\<lambda>(s, t). (1 - s, t))"
      have hG_eq: "G = F \<circ> \<phi>" unfolding G_def \<phi>_def comp_def by auto
      have h\<phi>_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology (I_set \<times> I_set) II_topology \<phi>"
      proof -
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
        have hid: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
            (I_set \<times> I_set) (product_topology_on I_top I_top) id"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> I_set \<times> I_set" thus "id p \<in> I_set \<times> I_set" by (by100 simp)
        next
          fix W assume hW: "W \<in> product_topology_on I_top I_top"
          \<comment> \<open>{p \<in> I^2. id p \<in> W} = I^2 \<inter> W. Since I^2 \<in> T and W \<in> T, intersection \<in> T.\<close>
          have hII_mem: "(I_set \<times> I_set) \<in> product_topology_on I_top I_top"
            using hTII[unfolded II_topology_def] unfolding is_topology_on_def by (by100 blast)
          have heq: "{p \<in> I_set \<times> I_set. id p \<in> W} = (I_set \<times> I_set) \<inter> W" by (by100 auto)
          show "{p \<in> I_set \<times> I_set. id p \<in> W} \<in> product_topology_on I_top I_top"
            unfolding heq
            by (rule topology_inter_open[OF hTII[unfolded II_topology_def] hII_mem hW])
        qed
        have hprojs: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
            I_set I_top (pi1 \<circ> id) \<and>
            top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
            I_set I_top (pi2 \<circ> id)"
          using iffD1[OF Theorem_18_4[OF hTII[unfolded II_topology_def] hTI hTI] hid] by (by100 simp)
        have hfst: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top fst"
          using hprojs unfolding II_topology_def pi1_def comp_def by (by100 simp)
        have hsnd: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top snd"
          using hprojs unfolding II_topology_def pi2_def comp_def by (by100 simp)
        have hrev: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
          by (rule op_minus_continuous_on_interval)
        have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top ((\<lambda>t. 1-t) \<circ> fst)"
          by (rule top1_continuous_map_on_comp[OF hfst hrev])
        have hpi1: "pi1 \<circ> \<phi> = (\<lambda>t. 1 - t) \<circ> fst"
          unfolding \<phi>_def pi1_def comp_def by (by100 auto)
        have hpi2: "pi2 \<circ> \<phi> = snd"
          unfolding \<phi>_def pi2_def comp_def by (by100 auto)
        have "top1_continuous_map_on (I_set \<times> I_set) II_topology
            (I_set \<times> I_set) (product_topology_on I_top I_top) \<phi>"
          using iffD2[OF Theorem_18_4[OF hTII hTI hTI]]
            hcomp[folded hpi1] hsnd[folded hpi2] by (by100 blast)
        thus ?thesis unfolding II_topology_def by (by100 simp)
      qed
      show ?thesis unfolding hG_eq by (rule top1_continuous_map_on_comp[OF h\<phi>_cont hF])
    qed
    show "\<forall>s\<in>I_set. G (s, 0) = top1_path_reverse f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "1 - s \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      show "G (s, 0) = top1_path_reverse f s"
        unfolding G_def top1_path_reverse_def using hF0 \<open>1 - s \<in> I_set\<close> by auto
    qed
    show "\<forall>s\<in>I_set. G (s, 1) = top1_path_reverse g s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "1 - s \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      thus "G (s, 1) = top1_path_reverse g s"
        unfolding G_def top1_path_reverse_def using hF1 by auto
    qed
    show "\<forall>t\<in>I_set. G (0, t) = a"
    proof
      fix t assume ht: "t \<in> I_set"
      show "G (0, t) = a" unfolding G_def using hFr ht by simp
    qed
    show "\<forall>t\<in>I_set. G (1, t) = a"
    proof
      fix t assume ht: "t \<in> I_set"
      show "G (1, t) = a" unfolding G_def using hFl ht by simp
    qed
  qed
qed
\<comment> \<open>Key algebraic fact for 63.5: in an infinite cyclic group,
   any two nontrivial elements have a common nonzero power.
   Applied here: if [f] and [g] are both nontrivial in \<pi>_1(X) \<cong> Z,
   then \<exists> m>0, k>0. [f]^m = [g]^k (or [f]^m = [g^{-1}]^k).
   This contradicts Theorem_63_1_c.\<close>
lemma infinite_cyclic_common_power:
  assumes "is_topology_on X TX"
      and "top1_is_loop_on X TX a f"
      and "top1_is_loop_on X TX a g"
      and "\<not> top1_path_homotopic_on X TX a a f (top1_constant_path a)"
      and "\<not> top1_path_homotopic_on X TX a a g (top1_constant_path a)"
      and "\<exists>gen. top1_is_loop_on X TX a gen \<and>
            (\<forall>h. top1_is_loop_on X TX a h \<longrightarrow>
              (\<exists>n::nat. top1_path_homotopic_on X TX a a h (top1_path_power gen a n) \<or>
               top1_path_homotopic_on X TX a a h (top1_path_power (top1_path_reverse gen) a n)))"
  shows "\<exists>m k. m > 0 \<and>
      (top1_path_homotopic_on X TX a a
        (top1_path_power f a m) (top1_path_power g a k) \<or>
       top1_path_homotopic_on X TX a a
        (top1_path_power f a m) (top1_path_power (top1_path_reverse g) a k))"
proof -
  obtain gen where hgen: "top1_is_loop_on X TX a gen"
      and hgen_generates: "\<forall>h. top1_is_loop_on X TX a h \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on X TX a a h (top1_path_power gen a n) \<or>
         top1_path_homotopic_on X TX a a h (top1_path_power (top1_path_reverse gen) a n))"
    using assms(6) by (by100 blast)
  \<comment> \<open>[f] = gen^n1 or (gen^{-1})^n1 for some n1.\<close>
  obtain n1 where hn1: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n1) \<or>
      top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n1)"
    using hgen_generates assms(2) by (by100 blast)
  obtain n2 where hn2: "top1_path_homotopic_on X TX a a g (top1_path_power gen a n2) \<or>
      top1_path_homotopic_on X TX a a g (top1_path_power (top1_path_reverse gen) a n2)"
    using hgen_generates assms(3) by (by100 blast)
  \<comment> \<open>n1 > 0 (since f nontrivial) and n2 > 0 (since g nontrivial).\<close>
  have hn1_pos: "n1 > 0"
  proof (rule ccontr)
    assume "\<not> n1 > 0" hence "n1 = 0" by simp
    hence "top1_path_homotopic_on X TX a a f (top1_constant_path a)"
      using hn1 by (simp add: top1_constant_path_def)
    thus False using assms(4) by simp
  qed
  have hn2_pos: "n2 > 0"
  proof (rule ccontr)
    assume "\<not> n2 > 0" hence "n2 = 0" by simp
    hence "top1_path_homotopic_on X TX a a g (top1_constant_path a)"
      using hn2 by (simp add: top1_constant_path_def)
    thus False using assms(5) by simp
  qed
  \<comment> \<open>Case analysis on signs. When both same sign: [f^n2] \<simeq> gen^{n1*n2} \<simeq> [g^n1].
     When opposite signs: need integer powers (path_reverse). Key facts used:
     - path_homotopic_path_power: f \<simeq> g \<Rightarrow> f^n \<simeq> g^n
     - path_power_mult: (f^m)^n \<simeq> f^{m*n}
     - Commutativity of nat multiplication: n1*n2 = n2*n1.\<close>
  have hf_path: "top1_is_path_on X TX a a f" using assms(2) unfolding top1_is_loop_on_def by simp
  have hg_path: "top1_is_path_on X TX a a g" using assms(3) unfolding top1_is_loop_on_def by simp
  have hgen_path: "top1_is_path_on X TX a a gen" using hgen unfolding top1_is_loop_on_def by simp
  have hgenn1: "top1_is_path_on X TX a a (top1_path_power gen a n1)"
    by (rule top1_path_power_is_path[OF assms(1) hgen])
  have hgenn2: "top1_is_path_on X TX a a (top1_path_power gen a n2)"
    by (rule top1_path_power_is_path[OF assms(1) hgen])
  \<comment> \<open>Handle the case where both f and g are positive powers of gen.\<close>
  show ?thesis using hn1 hn2
  proof (elim disjE)
    assume h1: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n1)"
       and h2: "top1_path_homotopic_on X TX a a g (top1_path_power gen a n2)"
    \<comment> \<open>[f^n2] \<simeq> (gen^n1)^n2 \<simeq> gen^{n1*n2} and [g^n1] \<simeq> (gen^n2)^n1 \<simeq> gen^{n2*n1} = gen^{n1*n2}.\<close>
    have hfn2: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power (top1_path_power gen a n1) a n2)"
      by (rule path_homotopic_path_power[OF assms(1) h1 hf_path hgenn1])
    have hgn1: "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
        (top1_path_power (top1_path_power gen a n2) a n1)"
      by (rule path_homotopic_path_power[OF assms(1) h2 hg_path hgenn2])
    have hmult1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen a n1) a n2) (top1_path_power gen a (n1 * n2))"
      by (rule path_power_mult[OF assms(1) hgen])
    have hmult2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen a n2) a n1) (top1_path_power gen a (n2 * n1))"
      by (rule path_power_mult[OF assms(1) hgen])
    have "n1 * n2 = n2 * n1" by simp
    have hfn2_eq: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power gen a (n1 * n2))"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2 hmult1])
    have hgn1_eq: "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
        (top1_path_power gen a (n1 * n2))"
    proof -
      have "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
          (top1_path_power gen a (n2 * n1))"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hgn1 hmult2])
      moreover have "n2 * n1 = n1 * n2" by (rule mult.commute)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>By symmetry+transitivity: [f^n2] \<simeq> gen^{n1*n2} \<simeq> [g^n1].\<close>
    have hgn1_sym: "top1_path_homotopic_on X TX a a
        (top1_path_power gen a (n1 * n2)) (top1_path_power g a n1)"
      by (rule Lemma_51_1_path_homotopic_sym[OF hgn1_eq])
    have "top1_path_homotopic_on X TX a a (top1_path_power f a n2) (top1_path_power g a n1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2_eq hgn1_sym])
    thus ?thesis using hn2_pos by (intro exI[of _ n2] exI[of _ n1]) blast
  next
    \<comment> \<open>Case 2: [f] = gen^n1, [g] = (gen\<inverse>)^n2. Then [f^n2] = gen^{n1*n2} = [(g\<inverse>)^n1].\<close>
    assume h1: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n1)"
       and h2: "top1_path_homotopic_on X TX a a g (top1_path_power (top1_path_reverse gen) a n2)"
    \<comment> \<open>g\<inverse> \<simeq> gen^n2 (reverse of (gen\<inverse>)^n2). Use path_reverse of g.\<close>
    have hfn2: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power (top1_path_power gen a n1) a n2)"
      by (rule path_homotopic_path_power[OF assms(1) h1 hf_path hgenn1])
    have hmult1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen a n1) a n2) (top1_path_power gen a (n1 * n2))"
      by (rule path_power_mult[OF assms(1) hgen])
    have hfn2_eq: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power gen a (n1 * n2))"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2 hmult1])
    \<comment> \<open>g\<inverse> \<simeq> gen^n2. Path power of g\<inverse>: (g\<inverse>)^n1 \<simeq> (gen^n2)^n1 \<simeq> gen^{n2*n1}.\<close>
    define g' where "g' = top1_path_reverse g"
    have hg'_loop: "top1_is_loop_on X TX a g'"
      unfolding g'_def by (rule top1_path_reverse_is_loop[OF assms(3)])
    have hg'_path: "top1_is_path_on X TX a a g'"
      using hg'_loop unfolding top1_is_loop_on_def by simp
    \<comment> \<open>g \<simeq> (gen\<inverse>)^n2, so g\<inverse> \<simeq> ((gen\<inverse>)^n2)\<inverse> \<simeq> gen^n2.
       But proving ((gen\<inverse>)^n2)\<inverse> \<simeq> gen^n2 is complex. Use sorry.\<close>
    have hg'_gen: "top1_path_homotopic_on X TX a a g' (top1_path_power gen a n2)"
    proof -
      define gen_inv where "gen_inv = top1_path_reverse gen"
      have hgi_loop: "top1_is_loop_on X TX a gen_inv"
        unfolding gen_inv_def by (rule top1_path_reverse_is_loop[OF hgen])
      have hgi_n2: "top1_is_path_on X TX a a (top1_path_power gen_inv a n2)"
        by (rule top1_path_power_is_path[OF assms(1) hgi_loop])
      \<comment> \<open>g \<simeq> gen_inv^n2, so g\<inverse> \<simeq> (gen_inv^n2)\<inverse>.\<close>
      have h_rev: "top1_path_homotopic_on X TX a a g' (top1_path_reverse (top1_path_power gen_inv a n2))"
        unfolding g'_def
        by (rule path_homotopic_reverse[OF assms(1) h2[folded gen_inv_def] hg_path hgi_n2])
      \<comment> \<open>(gen_inv^n2)\<inverse> \<simeq> (gen_inv\<inverse>)^n2 = gen^n2.\<close>
      have h_dist: "top1_path_homotopic_on X TX a a
          (top1_path_reverse (top1_path_power gen_inv a n2))
          (top1_path_power (top1_path_reverse gen_inv) a n2)"
        by (rule path_power_reverse[OF assms(1) hgi_loop])
      have "top1_path_reverse gen_inv = gen" unfolding gen_inv_def top1_path_reverse_def by auto
      hence "top1_path_power (top1_path_reverse gen_inv) a n2 = top1_path_power gen a n2" by simp
      thus ?thesis using Lemma_51_1_path_homotopic_trans[OF assms(1) h_rev h_dist] by simp
    qed
    have hg'n1: "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
        (top1_path_power (top1_path_power gen a n2) a n1)"
      by (rule path_homotopic_path_power[OF assms(1) hg'_gen hg'_path hgenn2])
    have hmult2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen a n2) a n1) (top1_path_power gen a (n2 * n1))"
      by (rule path_power_mult[OF assms(1) hgen])
    have hg'n1_eq: "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
        (top1_path_power gen a (n1 * n2))"
    proof -
      have "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
          (top1_path_power gen a (n2 * n1))"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hg'n1 hmult2])
      moreover have "n2 * n1 = n1 * n2" by (rule mult.commute)
      ultimately show ?thesis by simp
    qed
    have "top1_path_homotopic_on X TX a a (top1_path_power f a n2) (top1_path_power g' a n1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2_eq
          Lemma_51_1_path_homotopic_sym[OF hg'n1_eq]])
    thus ?thesis using hn2_pos unfolding g'_def
      by (intro exI[of _ n2] exI[of _ n1]) blast
  next
    \<comment> \<open>Case 3: [f] = (gen\<inverse>)^n1, [g] = gen^n2. Symmetric to case 2.\<close>
    assume h1: "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n1)"
       and h2: "top1_path_homotopic_on X TX a a g (top1_path_power gen a n2)"
    \<comment> \<open>[f^n2] \<simeq> ((gen\<inverse>)^n1)^n2 \<simeq> (gen\<inverse>)^{n1*n2}. [g^n1] \<simeq> gen^{n2*n1}.
       So [f^n2] \<simeq> (gen\<inverse>)^{n1*n2} and [(g\<inverse>)^n1] \<simeq> (gen\<inverse>)^{n2*n1}.
       Thus [f^n2] \<simeq> [(g\<inverse>)^n1].\<close>
    define gen' where "gen' = top1_path_reverse gen"
    have hgen'_loop: "top1_is_loop_on X TX a gen'"
      unfolding gen'_def by (rule top1_path_reverse_is_loop[OF hgen])
    have hgen'n1: "top1_is_path_on X TX a a (top1_path_power gen' a n1)"
      by (rule top1_path_power_is_path[OF assms(1) hgen'_loop])
    have hfn2: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power (top1_path_power gen' a n1) a n2)"
      using path_homotopic_path_power[OF assms(1) h1[folded gen'_def] hf_path hgen'n1] by simp
    have hmult1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen' a n1) a n2) (top1_path_power gen' a (n1 * n2))"
      by (rule path_power_mult[OF assms(1) hgen'_loop])
    have hfn2_eq: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power gen' a (n1 * n2))"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2 hmult1])
    \<comment> \<open>g\<inverse> \<simeq> (gen)^{-n2} = (gen\<inverse>)^n2 = gen'^n2.\<close>
    define g' where "g' = top1_path_reverse g"
    have hg'_loop: "top1_is_loop_on X TX a g'"
      unfolding g'_def by (rule top1_path_reverse_is_loop[OF assms(3)])
    have hg'_path: "top1_is_path_on X TX a a g'"
      using hg'_loop unfolding top1_is_loop_on_def by simp
    have hg'_gen': "top1_path_homotopic_on X TX a a g' (top1_path_power gen' a n2)"
    proof -
      \<comment> \<open>g \<simeq> gen^n2, so g\<inverse> \<simeq> (gen^n2)\<inverse> \<simeq> (gen\<inverse>)^n2 = gen'^n2.\<close>
      have h_rev: "top1_path_homotopic_on X TX a a g' (top1_path_reverse (top1_path_power gen a n2))"
        unfolding g'_def
        by (rule path_homotopic_reverse[OF assms(1) h2 hg_path hgenn2])
      have h_dist: "top1_path_homotopic_on X TX a a
          (top1_path_reverse (top1_path_power gen a n2))
          (top1_path_power (top1_path_reverse gen) a n2)"
        by (rule path_power_reverse[OF assms(1) hgen])
      show ?thesis using Lemma_51_1_path_homotopic_trans[OF assms(1) h_rev h_dist]
        unfolding gen'_def by simp
    qed
    have hgen'n2: "top1_is_path_on X TX a a (top1_path_power gen' a n2)"
      by (rule top1_path_power_is_path[OF assms(1) hgen'_loop])
    have hg'n1: "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
        (top1_path_power (top1_path_power gen' a n2) a n1)"
      by (rule path_homotopic_path_power[OF assms(1) hg'_gen' hg'_path hgen'n2])
    have hmult2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen' a n2) a n1) (top1_path_power gen' a (n2 * n1))"
      by (rule path_power_mult[OF assms(1) hgen'_loop])
    have hg'n1_eq: "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
        (top1_path_power gen' a (n1 * n2))"
    proof -
      have "top1_path_homotopic_on X TX a a (top1_path_power g' a n1)
          (top1_path_power gen' a (n2 * n1))"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hg'n1 hmult2])
      moreover have "n2 * n1 = n1 * n2" by (rule mult.commute)
      ultimately show ?thesis by simp
    qed
    have "top1_path_homotopic_on X TX a a (top1_path_power f a n2) (top1_path_power g' a n1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2_eq
          Lemma_51_1_path_homotopic_sym[OF hg'n1_eq]])
    thus ?thesis using hn2_pos unfolding g'_def
      by (intro exI[of _ n2] exI[of _ n1]) blast
  next
    assume h1: "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n1)"
       and h2: "top1_path_homotopic_on X TX a a g (top1_path_power (top1_path_reverse gen) a n2)"
    \<comment> \<open>Same as case 1 but with gen\<inverse>. [f^n2] \<simeq> (gen\<inverse>^n1)^n2 \<simeq> gen\<inverse>^{n1*n2} \<simeq> (gen\<inverse>^n2)^n1 \<simeq> [g^n1].\<close>
    define gen' where "gen' = top1_path_reverse gen"
    have hgen'_loop: "top1_is_loop_on X TX a gen'"
      unfolding gen'_def by (rule top1_path_reverse_is_loop[OF hgen])
    have hgen'n1: "top1_is_path_on X TX a a (top1_path_power gen' a n1)"
      by (rule top1_path_power_is_path[OF assms(1) hgen'_loop])
    have hgen'n2: "top1_is_path_on X TX a a (top1_path_power gen' a n2)"
      by (rule top1_path_power_is_path[OF assms(1) hgen'_loop])
    have hfn2: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power (top1_path_power gen' a n1) a n2)"
      using path_homotopic_path_power[OF assms(1) h1[folded gen'_def] hf_path hgen'n1] by simp
    have hgn1: "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
        (top1_path_power (top1_path_power gen' a n2) a n1)"
      using path_homotopic_path_power[OF assms(1) h2[folded gen'_def] hg_path hgen'n2] by simp
    have hmult1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen' a n1) a n2) (top1_path_power gen' a (n1 * n2))"
      by (rule path_power_mult[OF assms(1) hgen'_loop])
    have hmult2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_power gen' a n2) a n1) (top1_path_power gen' a (n2 * n1))"
      by (rule path_power_mult[OF assms(1) hgen'_loop])
    have hfn2_eq: "top1_path_homotopic_on X TX a a (top1_path_power f a n2)
        (top1_path_power gen' a (n1 * n2))"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2 hmult1])
    have hgn1_eq: "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
        (top1_path_power gen' a (n1 * n2))"
    proof -
      have "top1_path_homotopic_on X TX a a (top1_path_power g a n1)
          (top1_path_power gen' a (n2 * n1))"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hgn1 hmult2])
      moreover have "n2 * n1 = n1 * n2" by (rule mult.commute)
      ultimately show ?thesis by simp
    qed
    have "top1_path_homotopic_on X TX a a (top1_path_power f a n2) (top1_path_power g a n1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hfn2_eq
          Lemma_51_1_path_homotopic_sym[OF hgn1_eq]])
    thus ?thesis using hn2_pos by (intro exI[of _ n2] exI[of _ n1]) (by100 blast)
  qed
qed


(** from \<S>63 Theorem 63.2: an arc D in S^2 does not separate S^2.
    Munkres' proof: by contradiction + Theorem 63.1; use that \<pi>_1(S^2) is trivial. **)
text \<open>Helper: R^2 is locally path-connected (every open set has path-connected neighborhoods).\<close>
text \<open>Helper: an open ball in R^2 is path-connected (convex, straight-line paths stay inside).\<close>

text \<open>Helper: non-separation implies path exists between any two points.\<close>
lemma S2_nonsep_path_exists:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "closedin_on top1_S2 top1_S2_topology D"
      and "\<not> top1_separates_on top1_S2 top1_S2_topology D"
      and "a \<in> top1_S2 - D" and "b \<in> top1_S2 - D"
  shows "\<exists>f. top1_is_path_on (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a b f"
proof -
  have hne: "top1_S2 - D \<noteq> {}" using assms(4) by (by100 blast)
  have hpc: "top1_path_connected_on (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
  proof -
    have hconn: "top1_connected_on (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
      using assms(3) unfolding top1_separates_on_def by (by100 blast)
    have hTS2D: "is_topology_on (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
      using hconn unfolding top1_connected_on_def by (by100 blast)
    have hS2D_open: "top1_S2 - D \<in> top1_S2_topology"
      using closedin_complement_openin[OF assms(2)] unfolding openin_on_def by simp
    \<comment> \<open>S^2-D is lpc via: pick b'\<notin>S^2-D, S^2-{b'}\<cong>R^2 lpc, restrict to open S^2-D.\<close>
    have hlocp: "top1_locally_path_connected_on (top1_S2 - D)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
    proof (cases "D = {}")
      case True
      hence hS2D_eq: "top1_S2 - D = top1_S2" by simp
      \<comment> \<open>S^2 is simply connected, hence path-connected, hence connected.
         For lpc: pick any b \<in> S^2, S^2-{b} \<cong> R^2 is lpc and open in S^2.
         S^2 is covered by S^2-{north} and S^2-{south}, both lpc and open.
         Union of open lpc sets that cover = lpc.\<close>
      \<comment> \<open>S^2 is lpc: every point is in S^2-{N} or S^2-{S} (both open, \<cong> R^2, hence lpc).\<close>
      have hS2_lpc: "top1_locally_path_connected_on top1_S2 top1_S2_topology"
        unfolding top1_locally_path_connected_on_def
      proof (intro conjI ballI)
        show "is_topology_on top1_S2 top1_S2_topology"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      next
        fix x assume hx: "x \<in> top1_S2"
        \<comment> \<open>x \<noteq> north_pole or x \<noteq> south_pole (S^2 has \<ge> 2 points).\<close>
        define south where "south = (0::real, 0::real, -1::real)"
        have hs_S2: "south \<in> top1_S2" unfolding south_def top1_S2_def by simp
        have hn_S2: "north_pole \<in> top1_S2" unfolding north_pole_def top1_S2_def by simp
        have hns: "north_pole \<noteq> south" unfolding north_pole_def south_def by simp
        \<comment> \<open>Choose b = north_pole if x \<noteq> north_pole, else south.\<close>
        define b where "b = (if x \<noteq> north_pole then north_pole else south)"
        have hb_S2: "b \<in> top1_S2" unfolding b_def using hn_S2 hs_S2 by auto
        have hxb: "x \<noteq> b" unfolding b_def using hns by auto
        have hx_in: "x \<in> top1_S2 - {b}" using hx hxb by (by100 blast)
        \<comment> \<open>S^2-{b} is open in S^2 and lpc.\<close>
        have hS2b_open: "top1_S2 - {b} \<in> top1_S2_topology"
        proof -
          have "closedin_on top1_S2 top1_S2_topology {b}"
          proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff top1_S2_is_topology_on_strict])
            show "{b} \<subseteq> top1_S2" using hb_S2 by simp
            show "top1_compact_on {b} (subspace_topology top1_S2 top1_S2_topology {b})"
              unfolding top1_compact_on_def
            proof (intro conjI allI impI)
              show "is_topology_on {b} (subspace_topology top1_S2 top1_S2_topology {b})"
                by (rule subspace_topology_is_topology_on[OF
                    is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]])
                  (simp add: hb_S2)
            next
              fix Uc assume hUc: "Uc \<subseteq> subspace_topology top1_S2 top1_S2_topology {b} \<and> {b} \<subseteq> \<Union>Uc"
              then obtain U where hU: "U \<in> Uc" and "b \<in> U" by (by100 blast)
              show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {b} \<subseteq> \<Union>F"
                apply (rule exI[of _ "{U}"]) using hU \<open>b \<in> U\<close> by auto
            qed
          qed
          thus ?thesis using closedin_complement_openin unfolding openin_on_def by simp
        qed
        obtain h_st where hh_st: "top1_homeomorphism_on (top1_S2 - {b})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
            (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) h_st"
          using S2_minus_point_homeo_R2[OF hb_S2] by blast
        have hS2b_lpc: "top1_locally_path_connected_on (top1_S2 - {b})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
          by (rule homeomorphism_preserves_lpc[OF homeomorphism_inverse[OF hh_st] R2_locally_path_connected])
        \<comment> \<open>x is in S^2-{b} which is lpc. So x has lpc neighborhoods.\<close>
        show "top1_locally_path_connected_at top1_S2 top1_S2_topology x"
          unfolding top1_locally_path_connected_at_def
        proof (intro allI impI)
          fix U assume hU: "neighborhood_of x top1_S2 top1_S2_topology U \<and> U \<subseteq> top1_S2"
          hence hUo: "U \<in> top1_S2_topology" and hxU: "x \<in> U" unfolding neighborhood_of_def by auto
          \<comment> \<open>U \<inter> (S^2-{b}) is open in S^2-{b}, contains x.\<close>
          have hU_int: "U \<inter> (top1_S2 - {b}) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
          proof -
            have "(top1_S2 - {b}) \<inter> U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
              by (rule subspace_topology_memI[OF hUo])
            moreover have "(top1_S2 - {b}) \<inter> U = U \<inter> (top1_S2 - {b})" by (by100 blast)
            ultimately show ?thesis by simp
          qed
          have hx_int: "x \<in> U \<inter> (top1_S2 - {b})" using hxU hx_in by (by100 blast)
          \<comment> \<open>By S^2-{b} lpc: \<exists> pc V with x \<in> V \<subseteq> U \<inter> (S^2-{b}).\<close>
          have "top1_locally_path_connected_at (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) x"
            using hS2b_lpc hx_in unfolding top1_locally_path_connected_on_def by (by100 blast)
          hence "\<exists>V. neighborhood_of x (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) V
              \<and> V \<subseteq> U \<inter> (top1_S2 - {b}) \<and> V \<subseteq> top1_S2 - {b}
              \<and> top1_path_connected_on V (subspace_topology (top1_S2 - {b})
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) V)"
            unfolding top1_locally_path_connected_at_def
            using hU_int hx_int unfolding neighborhood_of_def by (by100 blast)
          then obtain V where hVo: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
              and hxV: "x \<in> V" and hVsub: "V \<subseteq> U \<inter> (top1_S2 - {b})" and hVS2b: "V \<subseteq> top1_S2 - {b}"
              and hVpc: "top1_path_connected_on V (subspace_topology (top1_S2 - {b})
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) V)"
            unfolding neighborhood_of_def by (by100 blast)
          \<comment> \<open>V is open in S^2 (open in S^2-{b} which is open in S^2).\<close>
          obtain W where hW: "W \<in> top1_S2_topology" and hV_eq: "V = (top1_S2 - {b}) \<inter> W"
            using hVo unfolding subspace_topology_def by (by100 blast)
          have hV_S2: "V \<in> top1_S2_topology"
          proof -
            have "V = (top1_S2 - {b}) \<inter> W" by (rule hV_eq)
            thus ?thesis using topology_inter2[OF
                is_topology_on_strict_imp[OF assms(1)] hS2b_open hW] hV_eq by simp
          qed
          have hVU: "V \<subseteq> U" using hVsub by (by100 blast)
          have hVS2: "V \<subseteq> top1_S2" using hVS2b by (by100 blast)
          \<comment> \<open>V pc in subspace of S^2 (subspace_topology_trans).\<close>
          have "subspace_topology (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) V
              = subspace_topology top1_S2 top1_S2_topology V"
            by (rule subspace_topology_trans[OF hVS2b])
          hence hVpc': "top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
            using hVpc by simp
          show "\<exists>V. neighborhood_of x top1_S2 top1_S2_topology V \<and> V \<subseteq> U \<and> V \<subseteq> top1_S2
               \<and> top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
            using hV_S2 hxV hVU hVS2 hVpc' unfolding neighborhood_of_def by (by100 blast)
        qed
      qed
      moreover have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
      proof (rule subspace_topology_self_carrier)
        show "\<forall>U\<in>top1_S2_topology. U \<subseteq> top1_S2"
          using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      qed
      ultimately show ?thesis using hS2D_eq by simp
    next
      case False
      then obtain b' where hb': "b' \<in> D" by (by100 blast)
      have hb'_S2: "b' \<in> top1_S2" using hb' assms(2) unfolding closedin_on_def by (by100 blast)
      obtain h_st where hh_st: "top1_homeomorphism_on (top1_S2 - {b'})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'}))
          (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) h_st"
        using S2_minus_point_homeo_R2[OF hb'_S2] by blast
      have hS2b_lpc: "top1_locally_path_connected_on (top1_S2 - {b'})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'}))"
        by (rule homeomorphism_preserves_lpc[OF homeomorphism_inverse[OF hh_st] R2_locally_path_connected])
      have hS2D_sub: "top1_S2 - D \<subseteq> top1_S2 - {b'}" using hb' by (by100 blast)
      have hS2D_open_in_S2b: "top1_S2 - D \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'})"
      proof -
        have "(top1_S2 - {b'}) \<inter> (top1_S2 - D) = top1_S2 - D" using hS2D_sub by (by100 blast)
        moreover have "(top1_S2 - {b'}) \<inter> (top1_S2 - D) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'})"
          by (rule subspace_topology_memI[OF hS2D_open])
        ultimately show ?thesis by simp
      qed
      have "top1_locally_path_connected_on (top1_S2 - D)
          (subspace_topology (top1_S2 - {b'}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'})) (top1_S2 - D))"
        by (rule open_subset_locally_path_connected[OF hS2b_lpc hS2D_open_in_S2b hS2D_sub])
      moreover have "subspace_topology (top1_S2 - {b'}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b'})) (top1_S2 - D)
          = subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)"
        by (rule subspace_topology_trans[OF hS2D_sub])
      ultimately show ?thesis by simp
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTS2D hconn hlocp hne])
  qed
  thus ?thesis using assms(4,5) unfolding top1_path_connected_on_def by (by100 blast)
qed

text \<open>Helper: not connected implies two points with no connecting path.\<close>
lemma not_connected_imp_no_path:
  assumes hT: "is_topology_on X TX"
      and hncn: "\<not> top1_connected_on X TX"
  shows "\<exists>a b. a \<in> X \<and> b \<in> X \<and> \<not> (\<exists>f. top1_is_path_on X TX a b f)"
proof -
  obtain U V where hU: "U \<in> TX" and hV: "V \<in> TX" and hUne: "U \<noteq> {}" and hVne: "V \<noteq> {}"
      and hdisj: "U \<inter> V = {}" and hcover: "U \<union> V = X"
    using hncn unfolding top1_connected_on_def using hT by (by100 blast)
  obtain a where ha: "a \<in> U" using hUne by (by100 blast)
  obtain b where hb: "b \<in> V" using hVne by (by100 blast)
  have haX: "a \<in> X" and hbX: "b \<in> X" using ha hb hcover by (by100 blast)+
  have hno_path: "\<not> (\<exists>f. top1_is_path_on X TX a b f)"
  proof
    assume "\<exists>f. top1_is_path_on X TX a b f"
    then obtain f where hf: "top1_is_path_on X TX a b f" by (by100 blast)
    \<comment> \<open>f(I) is connected (continuous image of connected [0,1]).\<close>
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      using hf unfolding top1_is_path_on_def by (by100 blast)
    have hI_conn: "top1_connected_on I_set I_top"
    proof -
      have "connected {0..1::real}" by (rule connected_Icc)
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "connected I_set" using \<open>connected {0..1::real}\<close> hI01 by simp
      thus ?thesis using top1_connected_on_subspace_openI
        unfolding top1_unit_interval_topology_def by (by100 blast)
    qed
    have hI_top: "is_topology_on I_set I_top"
      using hI_conn unfolding top1_connected_on_def by (by100 blast)
    have hfI_conn: "top1_connected_on (f ` I_set) (subspace_topology X TX (f ` I_set))"
      by (rule Theorem_23_5[OF hI_top hT hI_conn hf_cont])
    \<comment> \<open>f(I) meets both U and V.\<close>
    have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by auto
    have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by auto
    have hfa: "f 0 = a" using hf unfolding top1_is_path_on_def by (by100 blast)
    have hfb: "f 1 = b" using hf unfolding top1_is_path_on_def by (by100 blast)
    have hfI_U: "f ` I_set \<inter> U \<noteq> {}" using hfa h0I ha by (by100 blast)
    have hfI_V: "f ` I_set \<inter> V \<noteq> {}" using hfb h1I hb by (by100 blast)
    \<comment> \<open>f(I) \<inter> U and f(I) \<inter> V are open in subspace of f(I), nonempty, disjoint, cover f(I).\<close>
    have hfI_sub: "f ` I_set \<subseteq> X" using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    have hfIU_open: "f ` I_set \<inter> U \<in> subspace_topology X TX (f ` I_set)"
      by (rule subspace_topology_memI[OF hU])
    have hfIV_open: "f ` I_set \<inter> V \<in> subspace_topology X TX (f ` I_set)"
      by (rule subspace_topology_memI[OF hV])
    have hfI_disj: "(f ` I_set \<inter> U) \<inter> (f ` I_set \<inter> V) = {}" using hdisj by (by100 blast)
    have hfI_cover: "(f ` I_set \<inter> U) \<union> (f ` I_set \<inter> V) = f ` I_set"
      using hfI_sub hcover by (by100 blast)
    \<comment> \<open>This contradicts f(I) being connected.\<close>
    have "\<exists>U' V'. U' \<in> subspace_topology X TX (f ` I_set)
        \<and> V' \<in> subspace_topology X TX (f ` I_set)
        \<and> U' \<noteq> {} \<and> V' \<noteq> {} \<and> U' \<inter> V' = {} \<and> U' \<union> V' = f ` I_set"
      apply (rule exI[of _ "f ` I_set \<inter> U"])
      apply (rule exI[of _ "f ` I_set \<inter> V"])
      apply (intro conjI)
      apply (rule hfIU_open) apply (rule hfIV_open)
      apply (rule hfI_U) apply (rule hfI_V)
      apply (rule hfI_disj) apply (rule hfI_cover)
      done
    thus False using hfI_conn unfolding top1_connected_on_def by (by100 blast)
  qed
  show ?thesis using haX hbX hno_path by (by100 blast)
qed

lemma arc_in_S2_closed:
  assumes "D \<subseteq> top1_S2"
      and "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
  shows "closedin_on top1_S2 top1_S2_topology D"
proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
    top1_S2_is_topology_on_strict assms(1)])
  obtain h where hh: "top1_homeomorphism_on I_set I_top D
      (subspace_topology top1_S2 top1_S2_topology D) h"
    using assms(2) unfolding top1_is_arc_on_def by (by100 blast)
  have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
    by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
  have "compact I_set" unfolding hI01 by (rule compact_Icc)
  have hI_compact: "top1_compact_on I_set I_top"
    unfolding top1_unit_interval_topology_def
    using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
  have hcont: "top1_continuous_map_on I_set I_top D
      (subspace_topology top1_S2 top1_S2_topology D) h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTD: "is_topology_on D (subspace_topology top1_S2 top1_S2_topology D)"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have himg: "h ` I_set = D"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have "top1_compact_on (h ` I_set) (subspace_topology D
      (subspace_topology top1_S2 top1_S2_topology D) (h ` I_set))"
    by (rule top1_compact_on_continuous_image[OF hI_compact hTD hcont])
  hence "top1_compact_on D (subspace_topology D
      (subspace_topology top1_S2 top1_S2_topology D) D)"
    using himg by simp
  moreover have "subspace_topology D (subspace_topology top1_S2 top1_S2_topology D) D
      = subspace_topology top1_S2 top1_S2_topology D"
    by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
  ultimately show "top1_compact_on D (subspace_topology top1_S2 top1_S2_topology D)" by simp
qed

lemma arc_connected:
  assumes "top1_is_arc_on D TD"
  shows "top1_connected_on D TD"
proof -
  obtain h where hh: "top1_homeomorphism_on I_set I_top D TD h"
    using assms unfolding top1_is_arc_on_def by (by100 blast)
  have hI_conn: "top1_connected_on I_set I_top"
  proof -
    have "connected {0..1::real}" by (rule connected_Icc)
    have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
      by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
    have "connected I_set" using \<open>connected {0..1::real}\<close> hI01 by simp
    have "top1_connected_on I_set (subspace_topology UNIV top1_open_sets I_set)"
      using \<open>connected I_set\<close> top1_connected_on_subspace_openI by (by100 blast)
    thus ?thesis unfolding top1_unit_interval_topology_def by simp
  qed
  have hI_top: "is_topology_on I_set I_top"
    using hI_conn unfolding top1_connected_on_def by (by100 blast)
  have hTD: "is_topology_on D TD"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hcont: "top1_continuous_map_on I_set I_top D TD h"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have himg: "h ` I_set = D"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have "top1_connected_on (h ` I_set) (subspace_topology D TD (h ` I_set))"
    by (rule Theorem_23_5[OF hI_top hTD hI_conn hcont])
  hence "top1_connected_on D (subspace_topology D TD D)" using himg by simp
  moreover have "subspace_topology D TD D = TD"
  proof -
    have hTD_strict: "is_topology_on_strict D TD"
      using assms unfolding top1_is_arc_on_def by (by100 blast)
    show ?thesis by (rule subspace_topology_self_carrier)
       (use hTD_strict in \<open>unfold is_topology_on_strict_def, by100 blast\<close>)
  qed
  ultimately show ?thesis by simp
qed

lemma arc_split_at_midpoint:
  assumes hT: "is_topology_on_strict X TX"
      and hH: "is_hausdorff_on X TX"
      and hDX: "D \<subseteq> X"
      and hArc: "top1_is_arc_on D (subspace_topology X TX D)"
  shows "\<exists>d D1 D2. d \<in> D \<and> D = D1 \<union> D2 \<and> D1 \<inter> D2 = {d}
      \<and> top1_is_arc_on D1 (subspace_topology X TX D1)
      \<and> top1_is_arc_on D2 (subspace_topology X TX D2)"
proof -
  obtain h where hh: "top1_homeomorphism_on I_set I_top D (subspace_topology X TX D) h"
    using hArc unfolding top1_is_arc_on_def by (by100 blast)
  define d where "d = h (1/2 :: real)"
  define D1 where "D1 = h ` {t \<in> I_set. t \<le> 1/2}"
  define D2 where "D2 = h ` {t \<in> I_set. t \<ge> 1/2}"
  have hd_D: "d \<in> D"
  proof -
    have h12: "(1/2 :: real) \<in> I_set" unfolding top1_unit_interval_def by auto
    have hbij: "bij_betw h I_set D" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    thus ?thesis unfolding d_def using h12 hbij unfolding bij_betw_def by (by100 blast)
  qed
  have hD_union: "D = D1 \<union> D2"
  proof -
    have hbij: "bij_betw h I_set D" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have "I_set = {t \<in> I_set. t \<le> 1/2} \<union> {t \<in> I_set. t \<ge> 1/2}" by auto
    thus ?thesis unfolding D1_def D2_def using hbij unfolding bij_betw_def by (by100 blast)
  qed
  have hD_inter: "D1 \<inter> D2 = {d}"
  proof (rule set_eqI, rule iffI)
    fix x assume hx: "x \<in> D1 \<inter> D2"
    have hxD1: "x \<in> D1" and hxD2: "x \<in> D2" using hx by (by100 blast)+
    obtain s where hs: "s \<in> I_set" "s \<le> 1/2" "h s = x"
      using hxD1 unfolding D1_def by (by100 blast)
    obtain t where ht: "t \<in> I_set" "t \<ge> 1/2" "h t = x"
      using hxD2 unfolding D2_def by (by100 blast)
    have hinj: "inj_on h I_set" using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have "s = t" using hinj hs(1) ht(1) hs(3) ht(3) unfolding inj_on_def by (by100 blast)
    hence hs12: "s = 1/2" using hs(2) ht(2) by (by100 linarith)
    have "x = d" using hs(3) hs12 unfolding d_def by simp
    thus "x \<in> {d}" by simp
  next
    fix x assume "x \<in> {d}"
    hence "x = d" by simp
    have h12: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by auto
    have "d \<in> D1" unfolding D1_def d_def using h12 by (by100 blast)
    moreover have "d \<in> D2" unfolding D2_def d_def using h12 by (by100 blast)
    ultimately show "x \<in> D1 \<inter> D2" using \<open>x = d\<close> by (by100 blast)
  qed
  \<comment> \<open>Each half is an arc: [0,1/2] and [1/2,1] are homeomorphic to [0,1], compose with h.\<close>
  have hD1_arc: "top1_is_arc_on D1 (subspace_topology X TX D1)"
  proof -
    \<comment> \<open>g(t) = h(t/2) maps [0,1] onto D1 = h([0,1/2]).\<close>
    define g where "g = (\<lambda>t. h (t / 2))"
    have hg_img: "g ` I_set = D1"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> g ` I_set"
      then obtain t where ht: "t \<in> I_set" "x = g t" by (by100 blast)
      have "t/2 \<in> I_set" and "t/2 \<le> 1/2"
        using ht(1) unfolding top1_unit_interval_def by auto
      thus "x \<in> D1" unfolding D1_def g_def ht(2) using \<open>t/2 \<in> I_set\<close> \<open>t/2 \<le> 1/2\<close> by (by100 blast)
    next
      fix x assume "x \<in> D1"
      then obtain s where hs: "s \<in> I_set" "s \<le> 1/2" "h s = x" unfolding D1_def by (by100 blast)
      have "2*s \<in> I_set" using hs(1) hs(2) unfolding top1_unit_interval_def by auto
      moreover have "g (2*s) = x" unfolding g_def using hs(3) by simp
      ultimately show "x \<in> g ` I_set" by (by100 blast)
    qed
    have hg_inj: "inj_on g I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and "g s = g t"
      hence "h (s/2) = h (t/2)" unfolding g_def by simp
      have "s/2 \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      moreover have "t/2 \<in> I_set" using ht unfolding top1_unit_interval_def by auto
      moreover have hinj: "inj_on h I_set"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      ultimately have "s/2 = t/2" using \<open>h (s/2) = h (t/2)\<close> hinj unfolding inj_on_def by (by100 blast)
      thus "s = t" by simp
    qed
    \<comment> \<open>g = h \<circ> (\<lambda>t. t/2) is continuous [0,1] \<rightarrow> D \<rightarrow> D1.\<close>
    have hg_cont: "top1_continuous_map_on I_set I_top D1 (subspace_topology X TX D1) g"
    proof -
      \<comment> \<open>h is continuous [0,1] \<rightarrow> D (subspace of X).\<close>
      have hh_cont: "top1_continuous_map_on I_set I_top D (subspace_topology X TX D) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>t/2 maps [0,1] into [0,1], continuous.\<close>
      have hdiv2_maps: "\<forall>t\<in>I_set. t/2 \<in> I_set"
        unfolding top1_unit_interval_def by auto
      \<comment> \<open>g(t) = h(t/2) maps I_set into D1.\<close>
      have hg_maps: "\<forall>t\<in>I_set. g t \<in> D1"
      proof
        fix t assume ht: "t \<in> I_set"
        have "t/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
        moreover have "t/2 \<le> 1/2" using ht unfolding top1_unit_interval_def by auto
        ultimately have "t/2 \<in> {s \<in> I_set. s \<le> 1/2}" by (by100 blast)
        thus "g t \<in> D1" unfolding g_def D1_def by (by100 blast)
      qed
      \<comment> \<open>For continuity: preimage of V \<in> subspace X TX D1 under g is in I_top.\<close>
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume "t \<in> I_set" thus "g t \<in> D1" using hg_maps by (by100 blast)
      next
        fix V assume hV: "V \<in> subspace_topology X TX D1"
        \<comment> \<open>V = D1 \<inter> W for W \<in> TX. Since D1 \<subseteq> D, V' = D \<inter> W \<in> subspace X TX D.\<close>
        obtain W where hW: "W \<in> TX" and hV_eq: "V = D1 \<inter> W"
          using hV unfolding subspace_topology_def by (by100 blast)
        have hDW: "D \<inter> W \<in> subspace_topology X TX D" by (rule subspace_topology_memI[OF hW])
        \<comment> \<open>{t \<in> I. h(t/2) \<in> V} = {t \<in> I. h(t/2) \<in> D1 \<inter> W} = {t \<in> I. t/2 \<in> I \<and> t/2 \<le> 1/2 \<and> h(t/2) \<in> W}
           = {t \<in> I. h(t/2) \<in> W} (since t/2 \<le> 1/2 always and h(t/2) \<in> D1 iff h(t/2) \<in> W \<inter> D1).\<close>
        have hpre_eq: "{t \<in> I_set. g t \<in> V} = {t \<in> I_set. h (t/2) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. g t \<in> V}"
          hence ht: "t \<in> I_set" and "g t \<in> V" by auto
          thus "t \<in> {t \<in> I_set. h (t/2) \<in> W}" unfolding g_def hV_eq by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. h (t/2) \<in> W}"
          hence ht: "t \<in> I_set" and "h (t/2) \<in> W" by auto
          have "g t \<in> D1" using hg_maps ht by (by100 blast)
          hence "g t \<in> V" using \<open>h (t/2) \<in> W\<close> unfolding g_def hV_eq by (by100 blast)
          thus "t \<in> {t \<in> I_set. g t \<in> V}" using ht by (by100 blast)
        qed
        \<comment> \<open>{t \<in> I. h(t/2) \<in> W} = {t \<in> I. t/2 \<in> {s \<in> I. h s \<in> W}} (where {s \<in> I. h s \<in> W} \<in> I_top).\<close>
        have hpre_h: "{s \<in> I_set. h s \<in> D \<inter> W} \<in> I_top"
          using hh_cont hDW unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>Need: {t \<in> I. t/2 \<in> {s \<in> I. h s \<in> D \<inter> W}} \<in> I_top.\<close>
        \<comment> \<open>This is the preimage of an I_top-open set under t \<mapsto> t/2.\<close>
        \<comment> \<open>{t \<in> I. h(t/2) \<in> W} = {t \<in> I. h(t/2) \<in> D \<inter> W} (since h(t/2) \<in> D always).\<close>
        have hpre_eq2: "{t \<in> I_set. h (t/2) \<in> W} = {t \<in> I_set. h (t/2) \<in> D \<inter> W}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. h (t/2) \<in> W}"
          hence ht: "t \<in> I_set" and "h (t/2) \<in> W" by auto
          have "t/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
          have hbij: "bij_betw h I_set D" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have "h (t/2) \<in> D" using \<open>t/2 \<in> I_set\<close> hbij unfolding bij_betw_def by (by100 blast)
          thus "t \<in> {t \<in> I_set. h (t/2) \<in> D \<inter> W}" using ht \<open>h (t/2) \<in> W\<close> by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. h (t/2) \<in> D \<inter> W}" thus "t \<in> {t \<in> I_set. h (t/2) \<in> W}" by (by100 blast)
        qed
        \<comment> \<open>{t \<in> I. h(t/2) \<in> D\<inter>W} is the preimage of {s \<in> I. h s \<in> D\<inter>W} under t\<mapsto>t/2,
           intersected with I. {s \<in> I. h s \<in> D\<inter>W} \<in> I_top (from h continuous).
           I_top = subspace UNIV top1_open_sets I_set. So {s \<in> I. h s \<in> D\<inter>W} = I \<inter> U0 for U0 open.
           Then {t \<in> I. t/2 \<in> I \<inter> U0} = I \<inter> (\<lambda>t. t/2)^{-1}(U0). Since t\<mapsto>t/2 is continuous,
           (\<lambda>t. t/2)^{-1}(U0) is open. So I \<inter> (\<lambda>t. t/2)^{-1}(U0) \<in> I_top.\<close>
        obtain U0 where hU0: "U0 \<in> top1_open_sets" and hpre_h_eq: "{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0"
        proof -
          have hpre_mem: "{s \<in> I_set. h s \<in> D \<inter> W} \<in> I_top" by (rule hpre_h)
          have "{s \<in> I_set. h s \<in> D \<inter> W} \<in> {I_set \<inter> U | U. U \<in> top1_open_sets}"
            using hpre_mem unfolding top1_unit_interval_topology_def subspace_topology_def by simp
          then obtain U0 where "U0 \<in> top1_open_sets" "{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0"
            by (by100 blast)
          thus ?thesis using that by auto
        qed
        have "{t \<in> I_set. h (t/2) \<in> D \<inter> W} = {t \<in> I_set. t/2 \<in> I_set \<inter> U0}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. h (t/2) \<in> D \<inter> W}"
          hence ht: "t \<in> I_set" and "h (t/2) \<in> D \<inter> W" by auto
          have "t/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
          moreover have "t/2 \<in> U0" using \<open>h (t/2) \<in> D \<inter> W\<close> \<open>t/2 \<in> I_set\<close> hpre_h_eq by (by100 blast)
          ultimately show "t \<in> {t \<in> I_set. t/2 \<in> I_set \<inter> U0}" using ht by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. t/2 \<in> I_set \<inter> U0}"
          hence ht: "t \<in> I_set" and "t/2 \<in> I_set \<inter> U0" by auto
          hence "h (t/2) \<in> D \<inter> W" using hpre_h_eq by (by100 blast)
          thus "t \<in> {t \<in> I_set. h (t/2) \<in> D \<inter> W}" using ht by (by100 blast)
        qed
        moreover have "{t \<in> I_set. t/2 \<in> I_set \<inter> U0} = I_set \<inter> ((\<lambda>t. t/2) -` U0)"
          using hdiv2_maps by (by100 blast)
        moreover have "open U0" using hU0 unfolding top1_open_sets_def by (by100 blast)
        moreover have "open ((\<lambda>t::real. t/2) -` U0)"
        proof -
          have "continuous_on UNIV (\<lambda>t::real. t/2)" by (intro continuous_intros) simp
          thus ?thesis using \<open>open U0\<close> by (simp add: continuous_on_open_vimage[OF open_UNIV])
        qed
        moreover have "(\<lambda>t::real. t/2) -` U0 \<in> top1_open_sets"
          using \<open>open ((\<lambda>t::real. t/2) -` U0)\<close> unfolding top1_open_sets_def by (by100 blast)
        ultimately have "{t \<in> I_set. h (t/2) \<in> D \<inter> W} = I_set \<inter> ((\<lambda>t. t/2) -` U0)" by simp
        moreover have "I_set \<inter> ((\<lambda>t. t/2) -` U0) \<in> I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_memI) (rule \<open>(\<lambda>t::real. t/2) -` U0 \<in> top1_open_sets\<close>)
        ultimately have "{t \<in> I_set. h (t/2) \<in> D \<inter> W} \<in> I_top" by simp
        thus "{t \<in> I_set. g t \<in> V} \<in> I_top"
          using hpre_eq hpre_eq2 by simp
      qed
    qed
    have hI_compact: "top1_compact_on I_set I_top"
    proof -
      have "compact {0..1::real}" by (rule compact_Icc)
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact I_set" using \<open>compact {0..1::real}\<close> hI01 by simp
      have "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
      thus ?thesis unfolding top1_unit_interval_topology_def by simp
    qed
    have hI_top: "is_topology_on I_set I_top"
      unfolding top1_unit_interval_topology_def
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) (by100 simp)
    have hD1_sub: "D1 \<subseteq> X"
      using hDX hD_union unfolding D1_def by (by100 blast)
    have hTD1: "is_topology_on D1 (subspace_topology X TX D1)"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT] hD1_sub])
    have hD1_haus: "is_hausdorff_on D1 (subspace_topology X TX D1)"
    proof -
      have "is_hausdorff_on X TX" by (rule hH)
      thus ?thesis by (rule hausdorff_subspace[OF _ hD1_sub])
    qed
    have hg_bij: "bij_betw g I_set D1" unfolding bij_betw_def using hg_inj hg_img by (by100 blast)
    have "top1_homeomorphism_on I_set I_top D1 (subspace_topology X TX D1) g"
      by (rule Theorem_26_6[OF hI_top hTD1 hI_compact hD1_haus hg_cont hg_bij])
    moreover have "is_topology_on_strict D1 (subspace_topology X TX D1)"
      by (rule subspace_topology_is_strict[OF hT hD1_sub])
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  have hD2_arc: "top1_is_arc_on D2 (subspace_topology X TX D2)"
  proof -
    define g' where "g' = (\<lambda>t. h ((1 + t) / 2))"
    have hg'_img: "g' ` I_set = D2"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> g' ` I_set"
      then obtain t where ht: "t \<in> I_set" "x = g' t" by (by100 blast)
      have "(1+t)/2 \<in> I_set" and "(1+t)/2 \<ge> 1/2"
        using ht(1) unfolding top1_unit_interval_def by auto
      thus "x \<in> D2" unfolding D2_def g'_def ht(2)
        using \<open>(1+t)/2 \<in> I_set\<close> \<open>(1+t)/2 \<ge> 1/2\<close> by (by100 blast)
    next
      fix x assume "x \<in> D2"
      then obtain s where hs: "s \<in> I_set" "s \<ge> 1/2" "h s = x" unfolding D2_def by (by100 blast)
      have "2*s - 1 \<in> I_set" using hs(1) hs(2) unfolding top1_unit_interval_def by auto
      moreover have "g' (2*s - 1) = x" unfolding g'_def using hs(3) by simp
      ultimately show "x \<in> g' ` I_set" by (by100 blast)
    qed
    have hg'_inj: "inj_on g' I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and "g' s = g' t"
      hence "h ((1+s)/2) = h ((1+t)/2)" unfolding g'_def by simp
      have hs2: "(1+s)/2 \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      have ht2: "(1+t)/2 \<in> I_set" using ht unfolding top1_unit_interval_def by auto
      have hinj: "inj_on h I_set"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "(1+s)/2 = (1+t)/2"
        using hinj hs2 ht2 \<open>h ((1+s)/2) = h ((1+t)/2)\<close> unfolding inj_on_def by (by100 blast)
      thus "s = t" by simp
    qed
    have hD2_sub: "D2 \<subseteq> X" using hDX hD_union unfolding D2_def by (by100 blast)
    have hTD2: "is_topology_on D2 (subspace_topology X TX D2)"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT] hD2_sub])
    have hD2_haus: "is_hausdorff_on D2 (subspace_topology X TX D2)"
      by (rule hausdorff_subspace[OF hH hD2_sub])
    have hg'_bij: "bij_betw g' I_set D2"
      unfolding bij_betw_def using hg'_inj hg'_img by (by100 blast)
    \<comment> \<open>g' continuity: same argument as for g, with (1+t)/2 instead of t/2.\<close>
    have hg'_cont: "top1_continuous_map_on I_set I_top D2 (subspace_topology X TX D2) g'"
    proof -
      have hh_cont: "top1_continuous_map_on I_set I_top D (subspace_topology X TX D) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hdiv2_maps: "\<forall>t\<in>I_set. (1+t)/2 \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hg'_maps: "\<forall>t\<in>I_set. g' t \<in> D2"
      proof
        fix t assume ht: "t \<in> I_set"
        have "(1+t)/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
        moreover have "(1+t)/2 \<ge> 1/2" using ht unfolding top1_unit_interval_def by auto
        ultimately have "(1+t)/2 \<in> {s \<in> I_set. s \<ge> 1/2}" by (by100 blast)
        thus "g' t \<in> D2" unfolding g'_def D2_def by (by100 blast)
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume "t \<in> I_set" thus "g' t \<in> D2" using hg'_maps by (by100 blast)
      next
        fix V assume hV: "V \<in> subspace_topology X TX D2"
        obtain W where hW: "W \<in> TX" and hV_eq: "V = D2 \<inter> W"
          using hV unfolding subspace_topology_def by (by100 blast)
        have hDW: "D \<inter> W \<in> subspace_topology X TX D" by (rule subspace_topology_memI[OF hW])
        have hpre_mem: "{s \<in> I_set. h s \<in> D \<inter> W} \<in> I_top"
          using hh_cont hDW unfolding top1_continuous_map_on_def by (by100 blast)
        have "{s \<in> I_set. h s \<in> D \<inter> W} \<in> {I_set \<inter> U | U. U \<in> top1_open_sets}"
          using hpre_mem unfolding top1_unit_interval_topology_def subspace_topology_def by simp
        then obtain U0 where "U0 \<in> top1_open_sets" "{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0"
          by (by100 blast)
        have hpre_eq: "{t \<in> I_set. g' t \<in> V} = {t \<in> I_set. h ((1+t)/2) \<in> W}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. g' t \<in> V}"
          thus "t \<in> {t \<in> I_set. h ((1+t)/2) \<in> W}" unfolding g'_def hV_eq by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. h ((1+t)/2) \<in> W}"
          hence ht: "t \<in> I_set" and "h ((1+t)/2) \<in> W" by auto
          have "g' t \<in> D2" using hg'_maps ht by (by100 blast)
          thus "t \<in> {t \<in> I_set. g' t \<in> V}" using ht \<open>h ((1+t)/2) \<in> W\<close>
            unfolding g'_def hV_eq by (by100 blast)
        qed
        have hpre_eq2: "{t \<in> I_set. h ((1+t)/2) \<in> W} = {t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0}"
        proof (rule set_eqI, rule iffI)
          fix t assume "t \<in> {t \<in> I_set. h ((1+t)/2) \<in> W}"
          hence ht: "t \<in> I_set" and "h ((1+t)/2) \<in> W" by auto
          have ht2: "(1+t)/2 \<in> I_set" using hdiv2_maps ht by (by100 blast)
          have hbij: "bij_betw h I_set D" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          have "h ((1+t)/2) \<in> D" using ht2 hbij unfolding bij_betw_def by (by100 blast)
          hence "(1+t)/2 \<in> {s \<in> I_set. h s \<in> D \<inter> W}" using ht2 \<open>h ((1+t)/2) \<in> W\<close> by (by100 blast)
          hence "(1+t)/2 \<in> I_set \<inter> U0" using \<open>{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0\<close> by (by100 blast)
          thus "t \<in> {t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0}" using ht by (by100 blast)
        next
          fix t assume "t \<in> {t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0}"
          hence ht: "t \<in> I_set" and "(1+t)/2 \<in> I_set \<inter> U0" by auto
          hence "h ((1+t)/2) \<in> D \<inter> W"
            using \<open>{s \<in> I_set. h s \<in> D \<inter> W} = I_set \<inter> U0\<close> by (by100 blast)
          thus "t \<in> {t \<in> I_set. h ((1+t)/2) \<in> W}" using ht by (by100 blast)
        qed
        have "{t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0} = I_set \<inter> ((\<lambda>t. (1+t)/2) -` U0)"
          using hdiv2_maps by (by100 blast)
        moreover have "open U0" using \<open>U0 \<in> top1_open_sets\<close> unfolding top1_open_sets_def by (by100 blast)
        moreover have hopen_pre: "open ((\<lambda>t::real. (1+t)/2) -` U0)"
        proof -
          have "continuous_on UNIV (\<lambda>t::real. (1+t)/2)" by (intro continuous_intros) simp
          thus ?thesis using \<open>open U0\<close> by (simp add: continuous_on_open_vimage[OF open_UNIV])
        qed
        moreover have "(\<lambda>t::real. (1+t)/2) -` U0 \<in> top1_open_sets"
          using hopen_pre unfolding top1_open_sets_def by (by100 blast)
        moreover have "I_set \<inter> ((\<lambda>t. (1+t)/2) -` U0) \<in> I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_memI) (rule \<open>(\<lambda>t::real. (1+t)/2) -` U0 \<in> top1_open_sets\<close>)
        ultimately have "{t \<in> I_set. (1+t)/2 \<in> I_set \<inter> U0} \<in> I_top" by simp
        thus "{t \<in> I_set. g' t \<in> V} \<in> I_top" using hpre_eq hpre_eq2 by simp
      qed
    qed
    have hI_top: "is_topology_on I_set I_top"
      unfolding top1_unit_interval_topology_def
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) (by100 simp)
    have hI_compact: "top1_compact_on I_set I_top"
    proof -
      have "compact {0..1::real}" by (rule compact_Icc)
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact I_set" using \<open>compact {0..1::real}\<close> hI01 by simp
      have "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
      thus ?thesis unfolding top1_unit_interval_topology_def by simp
    qed
    have "top1_homeomorphism_on I_set I_top D2 (subspace_topology X TX D2) g'"
      by (rule Theorem_26_6[OF hI_top hTD2 hI_compact hD2_haus hg'_cont hg'_bij])
    moreover have "is_topology_on_strict D2 (subspace_topology X TX D2)"
      by (rule subspace_topology_is_strict[OF hT hD2_sub])
    ultimately show ?thesis unfolding top1_is_arc_on_def by (by100 blast)
  qed
  show ?thesis using hd_D hD_union hD_inter hD1_arc hD2_arc by (by100 blast)
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
  proof -
    have hTS2D: "is_topology_on (top1_S2 - (D1 \<union> D2))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2)))"
      by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF assms(1)]]) (by100 blast)
    have "\<exists>a b. a \<in> top1_S2 - (D1 \<union> D2) \<and> b \<in> top1_S2 - (D1 \<union> D2) \<and>
        \<not> (\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a b f)"
      by (rule not_connected_imp_no_path[OF hTS2D hsep[unfolded top1_separates_on_def]])
    thus ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>Since D1 doesn't separate, join a to b in S^2-D1: path \<alpha>.\<close>
  have ha_D1: "a \<in> top1_S2 - D1" using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  have hb_D1: "b \<in> top1_S2 - D1" using \<open>b \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  have ha_D2: "a \<in> top1_S2 - D2" using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  have hb_D2: "b \<in> top1_S2 - D2" using \<open>b \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  obtain \<alpha> where "top1_is_path_on (top1_S2 - D1)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a b \<alpha>"
    using S2_nonsep_path_exists[OF assms(1) assms(2) assms(5) ha_D1 hb_D1] by (by100 blast)
  \<comment> \<open>Since D2 doesn't separate, join b to a in S^2-D2: path \<beta>.\<close>
  obtain \<beta> where "top1_is_path_on (top1_S2 - D2)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) b a \<beta>"
    using S2_nonsep_path_exists[OF assms(1) assms(3) assms(6) hb_D2 ha_D2] by (by100 blast)
  \<comment> \<open>The loop f = \<alpha>*\<beta> lies in X=S^2-(D1\<inter>D2). By Theorem 63.1, [f] is nontrivial.
     Setup: X = S^2\(D1\<inter>D2), U = S^2\D1, V = S^2\D2.
     U \<union> V = X, U \<inter> V = S^2\(D1\<union>D2).
     A = path component of a in U\<inter>V, B = rest. Both open (lpc).
     \<alpha>: a\<rightarrow>b in U, \<beta>: b\<rightarrow>a in V. Theorem 63.1: \<alpha>*\<beta> nontrivial in \<pi>_1(X,a).\<close>
  have hf_nontrivial: "\<exists>f. top1_is_loop_on (top1_S2 - (D1 \<inter> D2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2))) a f
      \<and> \<not> top1_path_homotopic_on (top1_S2 - (D1 \<inter> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2))) a a f
          (top1_constant_path a)"
  proof -
    let ?X = "top1_S2 - (D1 \<inter> D2)"
    let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
    let ?U = "top1_S2 - D1" and ?V = "top1_S2 - D2"
    have hTS2: "is_topology_on top1_S2 top1_S2_topology"
      using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
    have hTX: "is_topology_on ?X ?TX"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    \<comment> \<open>U, V open in X.\<close>
    have hU_open: "openin_on ?X ?TX ?U"
    proof -
      have "closedin_on top1_S2 top1_S2_topology D1" by (rule assms(2))
      hence "top1_S2 - D1 \<in> top1_S2_topology"
        using hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have "?U \<subseteq> ?X" by (by100 blast)
      have "?U = ?X \<inter> (top1_S2 - D1)" by (by100 blast)
      hence "?U \<in> ?TX" using \<open>top1_S2 - D1 \<in> top1_S2_topology\<close>
        unfolding subspace_topology_def by (by100 blast)
      thus ?thesis using \<open>?U \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
    qed
    have hV_open: "openin_on ?X ?TX ?V"
    proof -
      have "closedin_on top1_S2 top1_S2_topology D2" by (rule assms(3))
      hence "top1_S2 - D2 \<in> top1_S2_topology"
        using hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have "?V \<subseteq> ?X" by (by100 blast)
      have "?V = ?X \<inter> (top1_S2 - D2)" by (by100 blast)
      hence "?V \<in> ?TX" using \<open>top1_S2 - D2 \<in> top1_S2_topology\<close>
        unfolding subspace_topology_def by (by100 blast)
      thus ?thesis using \<open>?V \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
    qed
    have hUV_eq: "?U \<union> ?V = ?X" by (by100 blast)
    \<comment> \<open>Decompose U \<inter> V into path component A of a and rest B.\<close>
    have hUV_inter: "?U \<inter> ?V = top1_S2 - (D1 \<union> D2)" by (by100 blast)
    \<comment> \<open>A = path component of a in U\<inter>V, B = rest.\<close>
    define A where "A = top1_path_component_of_on (?U \<inter> ?V)
        (subspace_topology ?X ?TX (?U \<inter> ?V)) a"
    define B where "B = (?U \<inter> ?V) - A"
    have ha_UV: "a \<in> ?U \<inter> ?V" using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
    have hb_UV: "b \<in> ?U \<inter> ?V" using \<open>b \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
    \<comment> \<open>a \<in> A, b \<notin> A (can't be connected to a), hence b \<in> B.\<close>
    have hTUV: "is_topology_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V))"
      by (rule subspace_topology_is_topology_on[OF hTX]) (by100 blast)
    have ha_A: "a \<in> A" unfolding A_def
      by (rule top1_path_component_of_on_self_mem[OF hTUV ha_UV])
    have hb_B: "b \<in> B"
    proof -
      have "b \<in> ?U \<inter> ?V" by (rule hb_UV)
      moreover have "b \<notin> A"
      proof
        assume "b \<in> A"
        \<comment> \<open>b \<in> A = path_component(a) means b connected to a in U\<inter>V = S^2\(D1\<union>D2).\<close>
        \<comment> \<open>But hab_sep says a,b NOT connected in S^2\(D1\<union>D2). Contradiction.\<close>
        hence "\<exists>f. top1_is_path_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a b f"
          unfolding A_def top1_path_component_of_on_def top1_in_same_path_component_on_def
          by simp
        moreover have "?U \<inter> ?V = top1_S2 - (D1 \<union> D2)" by (by100 blast)
        moreover have "subspace_topology ?X ?TX (?U \<inter> ?V)
            = subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))"
        proof -
          have "?U \<inter> ?V \<subseteq> ?X" by (by100 blast)
          have "subspace_topology ?X ?TX (?U \<inter> ?V)
              = subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
            by (rule subspace_topology_trans[OF \<open>?U \<inter> ?V \<subseteq> ?X\<close>])
          thus ?thesis using \<open>?U \<inter> ?V = top1_S2 - (D1 \<union> D2)\<close> by simp
        qed
        ultimately show False using hab_sep by simp
      qed
      ultimately show ?thesis unfolding B_def by (by100 blast)
    qed
    \<comment> \<open>A, B open in X (path components of lpc space are open).\<close>
    \<comment> \<open>A, B open: U\<inter>V is open in S^2, hence lpc. Path components of lpc = open.\<close>
    have hUV_open_S2: "?U \<inter> ?V \<in> top1_S2_topology"
    proof -
      have "top1_S2 - D1 \<in> top1_S2_topology"
        using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      moreover have "top1_S2 - D2 \<in> top1_S2_topology"
        using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      ultimately show ?thesis by (rule topology_inter_open[OF hTS2])
    qed
    have hUV_lpc: "top1_locally_path_connected_on (?U \<inter> ?V)
        (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
    proof -
      have "?U \<inter> ?V \<subseteq> top1_S2" by (by100 blast)
      show ?thesis by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hUV_open_S2 \<open>?U \<inter> ?V \<subseteq> top1_S2\<close>])
    qed
    have hUV_lpc': "top1_locally_path_connected_on (?U \<inter> ?V)
        (subspace_topology ?X ?TX (?U \<inter> ?V))"
    proof -
      have "?U \<inter> ?V \<subseteq> ?X" by (by100 blast)
      have "subspace_topology ?X ?TX (?U \<inter> ?V) = subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
        by (rule subspace_topology_trans[OF \<open>?U \<inter> ?V \<subseteq> ?X\<close>])
      thus ?thesis using hUV_lpc by simp
    qed
    have hA_open_UV: "A \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
      unfolding A_def
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTUV hUV_lpc' ha_UV])
    have hA_sub': "A \<subseteq> ?U \<inter> ?V" unfolding A_def
      by (rule top1_path_component_of_on_subset[OF hTUV ha_UV])
    have hA_open: "openin_on ?X ?TX A"
    proof -
      have hU_in_TX: "?U \<in> ?TX" using hU_open unfolding openin_on_def by (by100 blast)
      have hV_in_TX: "?V \<in> ?TX" using hV_open unfolding openin_on_def by (by100 blast)
      have hUV_in_TX: "?U \<inter> ?V \<in> ?TX" by (rule topology_inter_open[OF hTX hU_in_TX hV_in_TX])
      obtain W where "W \<in> ?TX" "A = (?U \<inter> ?V) \<inter> W"
        using hA_open_UV unfolding subspace_topology_def by (by100 blast)
      hence "A \<in> ?TX" using hUV_in_TX by (simp add: topology_inter_open[OF hTX])
      moreover have "A \<subseteq> ?X" using hA_sub' by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by (by100 blast)
    qed
    have hB_open: "openin_on ?X ?TX B"
    proof -
      \<comment> \<open>B = (U\<inter>V)\A. Show B open in subspace U\<inter>V, then lift to X.\<close>
      \<comment> \<open>In U\<inter>V (lpc), each path component is open.
         B = union of path components \<noteq> A. Each open. Union open.\<close>
      have hB_open_UV: "B \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
      proof -
        \<comment> \<open>(?U\<inter>?V) \ A = B. A open in U\<inter>V. A also closed (complement = union of open path comp).
           So B = (U\<inter>V)\A open in U\<inter>V.\<close>
        \<comment> \<open>Key: \<forall> path component P of U\<inter>V, P is open (lpc).
           B = \<Union>{P \<in> path_components. P \<noteq> A}. Union of opens.\<close>
        have "\<forall>x \<in> ?U \<inter> ?V. top1_path_component_of_on (?U \<inter> ?V)
            (subspace_topology ?X ?TX (?U \<inter> ?V)) x
            \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
          by (intro ballI top1_path_component_of_on_open_if_locally_path_connected[OF hTUV hUV_lpc'])
        \<comment> \<open>B = \<Union>{path_component(x) | x \<in> U\<inter>V, path_component(x) \<noteq> A}.\<close>
        have "B = \<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
            | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}"
        proof (rule set_eqI, rule iffI)
          fix y assume "y \<in> B"
          hence "y \<in> ?U \<inter> ?V" "y \<notin> A" unfolding B_def by auto
          have "y \<in> top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) y"
            by (rule top1_path_component_of_on_self_mem[OF hTUV \<open>y \<in> ?U \<inter> ?V\<close>])
          thus "y \<in> \<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}"
            using \<open>y \<in> ?U \<inter> ?V\<close> \<open>y \<notin> A\<close> by (by100 blast)
        next
          fix y assume "y \<in> \<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}"
          then obtain x where hx: "x \<in> ?U \<inter> ?V" "x \<notin> A"
              and hy: "y \<in> top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x"
            by (by100 blast)
          have "y \<in> ?U \<inter> ?V"
            using top1_path_component_of_on_subset[OF hTUV hx(1)] hy by (by100 blast)
          moreover have "y \<notin> A"
          proof
            assume "y \<in> A"
            \<comment> \<open>y \<in> A = path_comp(a) and y \<in> path_comp(x).
               Path components overlap \<Rightarrow> equal. So path_comp(x) = A. But x \<notin> A.
               x \<in> path_comp(x) = A. Contradiction.\<close>
            hence "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a y"
              unfolding A_def top1_path_component_of_on_def by simp
            have "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x y"
              using hy unfolding top1_path_component_of_on_def by simp
            \<comment> \<open>By symmetry+transitivity: a and x in same path component. So x \<in> A.\<close>
            have "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) y a"
              by (rule top1_in_same_path_component_on_sym[OF hTUV
                  \<open>top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a y\<close>])
            have "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x a"
              by (rule top1_in_same_path_component_on_trans[OF hTUV
                  \<open>top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x y\<close>
                  \<open>top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) y a\<close>])
            hence "top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a x"
              by (rule top1_in_same_path_component_on_sym[OF hTUV])
            have "x \<in> A" unfolding A_def top1_path_component_of_on_def
              using \<open>top1_in_same_path_component_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) a x\<close>
              by simp
            thus False using hx(2) by simp
          qed
          ultimately show "y \<in> B" unfolding B_def by (by100 blast)
        qed
        moreover have "\<forall>P \<in> {top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
            | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}.
            P \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
          using \<open>\<forall>x \<in> ?U \<inter> ?V. top1_path_component_of_on (?U \<inter> ?V)
              (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              \<in> subspace_topology ?X ?TX (?U \<inter> ?V)\<close> by (by100 blast)
        ultimately have "B \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
        proof -
          have hTUV_top: "is_topology_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V))"
            by (rule hTUV)
          have "{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A} \<subseteq> subspace_topology ?X ?TX (?U \<inter> ?V)"
            using \<open>\<forall>P \<in> _. P \<in> subspace_topology ?X ?TX (?U \<inter> ?V)\<close> by (by100 blast)
          hence "\<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
              | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A} \<in> subspace_topology ?X ?TX (?U \<inter> ?V)"
            using hTUV_top unfolding is_topology_on_def by (by100 blast)
          thus ?thesis
            using \<open>B = \<Union>{top1_path_component_of_on (?U \<inter> ?V) (subspace_topology ?X ?TX (?U \<inter> ?V)) x
                | x. x \<in> ?U \<inter> ?V \<and> x \<notin> A}\<close> by simp
        qed
        thus ?thesis .
      qed
      \<comment> \<open>B open in U\<inter>V + U\<inter>V open in X \<Rightarrow> B open in X.\<close>
      obtain W where "W \<in> ?TX" "B = (?U \<inter> ?V) \<inter> W"
        using hB_open_UV unfolding subspace_topology_def by (by100 blast)
      have hU_in_TX: "?U \<in> ?TX" using hU_open unfolding openin_on_def by (by100 blast)
      have hV_in_TX: "?V \<in> ?TX" using hV_open unfolding openin_on_def by (by100 blast)
      have hUV_in_TX: "?U \<inter> ?V \<in> ?TX" by (rule topology_inter_open[OF hTX hU_in_TX hV_in_TX])
      have "B \<in> ?TX" using \<open>B = (?U \<inter> ?V) \<inter> W\<close> \<open>W \<in> ?TX\<close> hUV_in_TX
        by (simp add: topology_inter_open[OF hTX])
      moreover have "B \<subseteq> ?X" unfolding B_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by (by100 blast)
    qed
    have hAB_disj: "A \<inter> B = {}" unfolding B_def by (by100 blast)
    have hAB_cover: "A \<union> B = ?U \<inter> ?V" unfolding B_def using hA_sub' by auto
    \<comment> \<open>Lift \<alpha> to path in U (subspace of X), \<beta> to path in V (subspace of X).
       Key: subspace X TX U = subspace S^2 S^2_top U (by transitivity, U \<subseteq> X).\<close>
    have hU_sub_X: "?U \<subseteq> ?X" by (by100 blast)
    have hV_sub_X: "?V \<subseteq> ?X" by (by100 blast)
    have hU_top_eq: "subspace_topology ?X ?TX ?U = subspace_topology top1_S2 top1_S2_topology ?U"
      by (rule subspace_topology_trans[OF hU_sub_X])
    have hV_top_eq: "subspace_topology ?X ?TX ?V = subspace_topology top1_S2 top1_S2_topology ?V"
      by (rule subspace_topology_trans[OF hV_sub_X])
    have h\<alpha>_U: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>"
      using \<open>top1_is_path_on (top1_S2 - D1)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a b \<alpha>\<close>
      hU_top_eq by simp
    have h\<beta>_V: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>"
      using \<open>top1_is_path_on (top1_S2 - D2)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) b a \<beta>\<close>
      hV_top_eq by simp
    \<comment> \<open>Apply Theorem 63.1: \<alpha>*\<beta> nontrivial in \<pi>_1(X,a).\<close>
    have "\<not> top1_path_homotopic_on ?X ?TX a a
        (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    proof (rule Theorem_63_1_loop_nontrivial)
      show "is_topology_on ?X ?TX" by (rule hTX)
      show "openin_on ?X ?TX ?U" by (rule hU_open)
      show "openin_on ?X ?TX ?V" by (rule hV_open)
      show "?U \<union> ?V = ?X" by (rule hUV_eq)
      show "?U \<inter> ?V = A \<union> B" using hAB_cover by simp
      show "A \<inter> B = {}" by (rule hAB_disj)
      show "openin_on ?X ?TX A" by (rule hA_open)
      show "openin_on ?X ?TX B" by (rule hB_open)
      show "a \<in> A" by (rule ha_A)
      show "b \<in> B" by (rule hb_B)
      show "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>" by (rule h\<alpha>_U)
      show "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>" by (rule h\<beta>_V)
    qed
    moreover have "top1_is_loop_on ?X ?TX a (top1_path_product \<alpha> \<beta>)"
    proof -
      \<comment> \<open>\<alpha> path in U (\<subseteq> X) \<Rightarrow> \<alpha> path in X. \<beta> path in V (\<subseteq> X) \<Rightarrow> \<beta> path in X.\<close>
      have hTX_strict: "is_topology_on_strict ?X ?TX"
        by (rule subspace_topology_is_strict[OF assms(1)]) (by100 blast)
      have h\<alpha>_X: "top1_is_path_on ?X ?TX a b \<alpha>"
        by (rule path_in_subspace_imp_path_in_ambient[OF hTX_strict _ h\<alpha>_U]) (by100 blast)
      have h\<beta>_X: "top1_is_path_on ?X ?TX b a \<beta>"
        by (rule path_in_subspace_imp_path_in_ambient[OF hTX_strict _ h\<beta>_V]) (by100 blast)
      have "top1_is_path_on ?X ?TX a a (top1_path_product \<alpha> \<beta>)"
        by (rule top1_path_product_is_path[OF hTX h\<alpha>_X h\<beta>_X])
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>But S^2-(D1\<inter>D2) is simply connected by assumption. Contradiction.\<close>
  have ha_mem: "a \<in> top1_S2 - (D1 \<inter> D2)"
    using \<open>a \<in> top1_S2 - (D1 \<union> D2)\<close> by (by100 blast)
  show False using hf_nontrivial assms(4) ha_mem
    unfolding top1_simply_connected_on_def by (by100 blast)
qed


\<comment> \<open>Munkres' joining lemma (used in second proof of 63.2):
   If D = D1 \<union> D2 with D1 \<inter> D2 = {d}, and a,b can be joined by paths in
   S^2-D1 and S^2-D2, then they can be joined by a path in S^2-D.
   Proof: if not, apply Theorem 63.1 to X = S^2-{d}, U = S^2-D1, V = S^2-D2.
   U \<inter> V = S^2-D contains a,b (disconnected). Let A = path-component of a in U\<inter>V.
   B = rest. Then \<alpha>*\<beta> is nontrivial in \<pi>_1(S^2-{d}). But S^2-{d} simply connected.\<close>
lemma arc_joining_lemma:
  assumes hT: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hD1_sub: "D1 \<subseteq> top1_S2" and hD2_sub: "D2 \<subseteq> top1_S2"
      and hD1_closed: "closedin_on top1_S2 top1_S2_topology D1"
      and hD2_closed: "closedin_on top1_S2 top1_S2_topology D2"
      and hD_inter: "D1 \<inter> D2 = {d}"
      and hd_S2: "d \<in> top1_S2"
      and hab: "a \<in> top1_S2 - (D1 \<union> D2)" "b \<in> top1_S2 - (D1 \<union> D2)"
      and hab_D1: "\<exists>f. top1_is_path_on (top1_S2 - D1)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a b f"
      and hab_D2: "\<exists>f. top1_is_path_on (top1_S2 - D2)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) a b f"
  shows "\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a b f"
proof (rule ccontr)
  assume hnot: "\<not> ?thesis"
  let ?X = "top1_S2 - {d}"
  let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
  let ?U = "top1_S2 - D1" and ?V = "top1_S2 - D2"
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using hT unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>U, V open in S^2 (complements of closed sets).\<close>
  have hU_open: "?U \<in> top1_S2_topology"
    using hD1_closed hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  have hV_open: "?V \<in> top1_S2_topology"
    using hD2_closed hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  \<comment> \<open>X = U \<union> V, U \<inter> V = S^2 - D.\<close>
  have hUV: "?U \<union> ?V = ?X" using hD_inter by (by100 blast)
  have hUV_inter: "?U \<inter> ?V = top1_S2 - (D1 \<union> D2)" by (by100 blast)
  \<comment> \<open>a, b \<in> U \<inter> V but not path-connected in U \<inter> V.\<close>
  have hab_UV: "a \<in> ?U \<inter> ?V" "b \<in> ?U \<inter> ?V"
    using hab hD_inter by auto
  \<comment> \<open>U \<inter> V is open in S^2 hence lpc. Components = path components.\<close>
  have hUV_open: "?U \<inter> ?V \<in> top1_S2_topology"
    by (rule topology_inter_open[OF hTS2 hU_open hV_open])
  have hlpc: "top1_locally_path_connected_on (?U \<inter> ?V)
      (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hUV_open]) (by100 blast)
  \<comment> \<open>Let A = path-component of a in U \<inter> V. B = rest of U \<inter> V.\<close>
  \<comment> \<open>A and B are open (components of lpc space). a \<in> A, b \<in> B.\<close>
  \<comment> \<open>A \<union> B = U \<inter> V, A \<inter> B = {}.\<close>
  \<comment> \<open>Get paths \<alpha>: a \<rightarrow> b in U, \<beta>: b \<rightarrow> a in V.\<close>
  \<comment> \<open>By Theorem 63.1(a): \<alpha>*\<beta> nontrivial in \<pi>_1(X, a).\<close>
  \<comment> \<open>But X = S^2-{d} simply connected. Contradiction.\<close>
  \<comment> \<open>Step 1: A = path-component of a, B = rest.\<close>
  define PC_a :: "(real \<times> real \<times> real) set" where "PC_a = top1_path_component_of_on (?U \<inter> ?V)
      (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a"
  define Rest :: "(real \<times> real \<times> real) set" where "Rest = (?U \<inter> ?V) - PC_a"
  have ha_UV: "a \<in> ?U \<inter> ?V" using hab hD_inter by auto
  have hb_UV: "b \<in> ?U \<inter> ?V" using hab hD_inter by auto
  have hT_UV: "is_topology_on (?U \<inter> ?V)
      (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
    by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
  have ha_PC: "a \<in> PC_a"
  proof -
    have "top1_in_same_path_component_on (?U \<inter> ?V)
        (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a a"
      unfolding top1_in_same_path_component_on_def
      using top1_constant_path_is_path[OF hT_UV ha_UV] by (by100 blast)
    thus ?thesis unfolding PC_a_def top1_path_component_of_on_def by (by100 blast)
  qed
  have hb_Rest: "b \<in> Rest"
  proof -
    have "\<not> (\<exists>f. top1_is_path_on (?U \<inter> ?V) (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a b f)"
      using hnot hUV_inter by simp
    hence "b \<notin> PC_a" unfolding PC_a_def top1_path_component_of_on_def
        top1_in_same_path_component_on_def by (by100 blast)
    thus ?thesis unfolding Rest_def using hb_UV by (by100 blast)
  qed
  have hPC_sub: "PC_a \<subseteq> ?U \<inter> ?V"
  proof
    fix y assume "y \<in> PC_a"
    hence "\<exists>f. top1_is_path_on (?U \<inter> ?V)
        (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a y f"
      unfolding PC_a_def top1_path_component_of_on_def top1_in_same_path_component_on_def
      by simp
    then obtain f where "top1_is_path_on (?U \<inter> ?V)
        (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) a y f" by blast
    hence "f 1 = y" "f 1 \<in> ?U \<inter> ?V"
      unfolding top1_is_path_on_def top1_continuous_map_on_def
        top1_unit_interval_def by auto
    thus "y \<in> ?U \<inter> ?V" by simp
  qed
  have hPC_open_UV: "PC_a \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
    unfolding PC_a_def
    by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hT_UV hlpc ha_UV])
  have hUV_open_X: "openin_on ?X ?TX (?U \<inter> ?V)"
  proof -
    have "?U \<inter> ?V \<subseteq> ?X" using hD_inter by (by100 blast)
    have "?U \<inter> ?V = ?X \<inter> (?U \<inter> ?V)" using hD_inter by (by100 blast)
    hence "?U \<inter> ?V \<in> ?TX" using hUV_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using \<open>?U \<inter> ?V \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
  qed
  have hPC_open: "openin_on ?X ?TX PC_a"
  proof -
    \<comment> \<open>PC_a open in U\<inter>V. U\<inter>V open in X. Open-in-open = open.\<close>
    have hPC_open_in_UV: "openin_on (?U \<inter> ?V) (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)) PC_a"
      using hPC_open_UV hPC_sub unfolding openin_on_def by (by100 blast)
    \<comment> \<open>Transfer: subspace of S^2 restricted to U\<inter>V = subspace of X restricted to U\<inter>V.\<close>
    have hUV_sub_X: "?U \<inter> ?V \<subseteq> ?X" using hD_inter by (by100 blast)
    \<comment> \<open>PC_a open in U\<inter>V (S^2-sub). Transfer to X.\<close>
    have "PC_a \<in> ?TX"
    proof -
      have "PC_a \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)" by (rule hPC_open_UV)
      then obtain W where hW_mem: "W \<in> top1_S2_topology" and hPC_W: "PC_a = (?U \<inter> ?V) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "(?U \<inter> ?V) \<inter> W \<in> top1_S2_topology"
        by (rule topology_inter_open[OF hTS2 hUV_open hW_mem])
      have "PC_a = ?X \<inter> ((?U \<inter> ?V) \<inter> W)"
        using hPC_W hPC_sub hUV_sub_X by (by100 blast)
      thus ?thesis using \<open>(?U \<inter> ?V) \<inter> W \<in> top1_S2_topology\<close>
        unfolding subspace_topology_def by (by100 blast)
    qed
    thus ?thesis using hPC_sub hUV_sub_X unfolding openin_on_def by (by100 blast)
  qed
  have hRest_open: "openin_on ?X ?TX Rest"
  proof -
    have hRest_sub: "Rest \<subseteq> ?U \<inter> ?V" unfolding Rest_def by (by100 blast)
    have hUV_sub_X: "?U \<inter> ?V \<subseteq> ?X" using hD_inter by (by100 blast)
    have hRest_open_UV: "Rest \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
    proof -
      have "(?U \<inter> ?V) - PC_a \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
        unfolding PC_a_def
        by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hT_UV hlpc ha_UV])
      thus ?thesis unfolding Rest_def by simp
    qed
    obtain W where "W \<in> subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
        and "Rest = (?U \<inter> ?V) \<inter> W"
      using hRest_open_UV hRest_sub unfolding subspace_topology_def by (by100 blast)
    obtain W0 where "W0 \<in> top1_S2_topology" and hW0: "W = (?U \<inter> ?V) \<inter> W0"
      using \<open>W \<in> _\<close> unfolding subspace_topology_def by (by100 blast)
    have "Rest = (?U \<inter> ?V) \<inter> W0"
      using \<open>Rest = (?U \<inter> ?V) \<inter> W\<close> hW0 hRest_sub by (by100 blast)
    have "(?U \<inter> ?V) \<inter> W0 \<in> top1_S2_topology"
      by (rule topology_inter_open[OF hTS2 hUV_open \<open>W0 \<in> top1_S2_topology\<close>])
    have "Rest = ?X \<inter> ((?U \<inter> ?V) \<inter> W0)"
      using \<open>Rest = (?U \<inter> ?V) \<inter> W0\<close> hRest_sub hUV_sub_X by (by100 blast)
    hence "Rest \<in> ?TX" using \<open>(?U \<inter> ?V) \<inter> W0 \<in> top1_S2_topology\<close>
      unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using hRest_sub hUV_sub_X unfolding openin_on_def by (by100 blast)
  qed
  have hPCR_cover: "PC_a \<union> Rest = ?U \<inter> ?V"
    unfolding Rest_def using hPC_sub by (by100 blast)
  have hPCR_disj: "PC_a \<inter> Rest = {}" unfolding Rest_def by (by100 blast)
  \<comment> \<open>Step 2: Get paths \<alpha> and \<beta>.\<close>
  \<comment> \<open>Step 2: Get paths \<alpha> and \<beta>. Need them with subspace_topology X TX U.\<close>
  have hU_sub_X: "?U \<subseteq> ?X" using hD_inter by (by100 blast)
  have hV_sub_X: "?V \<subseteq> ?X" using hD_inter by (by100 blast)
  have hTU_eq: "subspace_topology ?X ?TX ?U = subspace_topology top1_S2 top1_S2_topology ?U"
    by (rule subspace_topology_trans[OF hU_sub_X])
  have hTV_eq: "subspace_topology ?X ?TX ?V = subspace_topology top1_S2 top1_S2_topology ?V"
    by (rule subspace_topology_trans[OF hV_sub_X])
  obtain \<alpha> where h\<alpha>: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>"
  proof -
    obtain f where "top1_is_path_on ?U (subspace_topology top1_S2 top1_S2_topology ?U) a b f"
      using hab_D1 by blast
    hence "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b f" using hTU_eq by simp
    thus ?thesis using that by blast
  qed
  obtain \<beta> where h\<beta>: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>"
  proof -
    obtain f where hf: "top1_is_path_on ?V (subspace_topology top1_S2 top1_S2_topology ?V) a b f"
      using hab_D2 by blast
    \<comment> \<open>Reverse: path b \<rightarrow> a from path a \<rightarrow> b.\<close>
    have "top1_is_path_on ?V (subspace_topology top1_S2 top1_S2_topology ?V) b a (top1_path_reverse f)"
      by (rule top1_path_reverse_is_path[OF hf])
    hence "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a (top1_path_reverse f)"
      using hTV_eq by simp
    thus ?thesis using that by blast
  qed
  \<comment> \<open>Step 3: Apply Theorem 63.1(a).\<close>
  have hX_TX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
  have hU_open_X: "openin_on ?X ?TX ?U"
  proof -
    have "?U \<subseteq> ?X" using hD_inter by (by100 blast)
    have "?U = ?X \<inter> ?U" using hD_inter by (by100 blast)
    hence "?U \<in> ?TX" using hU_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using \<open>?U \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
  qed
  have hV_open_X: "openin_on ?X ?TX ?V"
  proof -
    have "?V \<subseteq> ?X" using hD_inter by (by100 blast)
    have "?V = ?X \<inter> ?V" using hD_inter by (by100 blast)
    hence "?V \<in> ?TX" using hV_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis using \<open>?V \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
  qed
  have hnontrivial: "\<not> top1_path_homotopic_on ?X ?TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
  proof (rule Theorem_63_1_loop_nontrivial)
    show "is_topology_on ?X ?TX" by (rule hX_TX)
    show "openin_on ?X ?TX ?U" by (rule hU_open_X)
    show "openin_on ?X ?TX ?V" by (rule hV_open_X)
    show "?U \<union> ?V = ?X" by (rule hUV)
    show "?U \<inter> ?V = PC_a \<union> Rest" using hPCR_cover by simp
    show "PC_a \<inter> Rest = {}" by (rule hPCR_disj)
    show "openin_on ?X ?TX PC_a" by (rule hPC_open)
    show "openin_on ?X ?TX Rest" by (rule hRest_open)
    show "a \<in> PC_a" by (rule ha_PC)
    show "b \<in> Rest" by (rule hb_Rest)
    show "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>" by (rule h\<alpha>)
    show "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>" by (rule h\<beta>)
  qed
  \<comment> \<open>Step 4: But X = S^2-{d} simply connected.\<close>
  have hsc: "top1_simply_connected_on ?X ?TX"
    by (rule S2_minus_point_simply_connected[OF hd_S2])
  have "top1_path_homotopic_on ?X ?TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
  proof -
    have ha_X: "a \<in> ?X" using hab hD_inter by (by100 blast)
    have hab_loop: "top1_is_loop_on ?X ?TX a (top1_path_product \<alpha> \<beta>)"
    proof -
      have hTX_strict: "is_topology_on_strict ?X ?TX"
        by (rule subspace_topology_is_strict[OF hT]) (by100 blast)
      have h\<alpha>_X: "top1_is_path_on ?X ?TX a b \<alpha>"
        by (rule path_in_subspace_imp_path_in_ambient[OF hTX_strict hU_sub_X h\<alpha>])
      have h\<beta>_X: "top1_is_path_on ?X ?TX b a \<beta>"
        by (rule path_in_subspace_imp_path_in_ambient[OF hTX_strict hV_sub_X h\<beta>])
      have hprod: "top1_is_path_on ?X ?TX a a (top1_path_product \<alpha> \<beta>)"
        by (rule top1_path_product_is_path[OF hX_TX h\<alpha>_X h\<beta>_X])
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    show ?thesis using hsc ha_X hab_loop
      unfolding top1_simply_connected_on_def by (by100 blast)
  qed
  thus False using \<open>\<not> top1_path_homotopic_on ?X ?TX a a _ _\<close> by contradiction
qed

theorem Theorem_63_2_arc_no_separation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "D \<subseteq> top1_S2"
  and "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology D"
proof -
  \<comment> \<open>Munkres 63.2 SECOND proof (bisection + Theorem 63.3).
     Assume D separates. Split D = D1 \<union> D2 at midpoint d.
     By Theorem 63.3 contrapositive: since D separates and S^2\{d} simply connected,
     at least one of D1, D2 separates (assuming neither does → D doesn't).
     Repeat bisection. Get nested arcs D \<supset> D1 \<supset> D2 \<supset> ..., each separating,
     shrinking to a single point x. But S^2\{x} \<cong> R^2, hence a,b connected there.
     Path avoids h(x), hence avoids h(I_n) for large n. Contradiction.\<close>
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence hsep: "top1_separates_on top1_S2 top1_S2_topology D" by simp
    \<comment> \<open>Split D = D1 \<union> D2 at midpoint.\<close>
    obtain d D1 D2 where hd: "d \<in> D" and hD: "D = D1 \<union> D2" and hD12: "D1 \<inter> D2 = {d}"
        and hD1_arc: "top1_is_arc_on D1 (subspace_topology top1_S2 top1_S2_topology D1)"
        and hD2_arc: "top1_is_arc_on D2 (subspace_topology top1_S2 top1_S2_topology D2)"
      using arc_split_at_midpoint[OF assms(1) top1_S2_is_hausdorff assms(2) assms(3)] by (by100 blast)
    have hd_S2: "d \<in> top1_S2" using hd assms(2) by (by100 blast)
    \<comment> \<open>D1, D2 are closed in S^2 (compact subsets of Hausdorff).\<close>
    have hD1_sub: "D1 \<subseteq> top1_S2" using assms(2) hD by (by100 blast)
    have hD2_sub: "D2 \<subseteq> top1_S2" using assms(2) hD by (by100 blast)
    have hD1_closed: "closedin_on top1_S2 top1_S2_topology D1"
      by (rule arc_in_S2_closed[OF hD1_sub hD1_arc])
    have hD2_closed: "closedin_on top1_S2 top1_S2_topology D2"
      by (rule arc_in_S2_closed[OF hD2_sub hD2_arc])
    \<comment> \<open>S^2\{d} simply connected.\<close>
    have hsc: "top1_simply_connected_on (top1_S2 - {d})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {d}))"
      by (rule S2_minus_point_simply_connected[OF hd_S2])
    \<comment> \<open>D1 \<inter> D2 = {d} so S^2\(D1\<inter>D2) = S^2\{d} simply connected.\<close>
    have "top1_S2 - (D1 \<inter> D2) = top1_S2 - {d}" using hD12 by simp
    hence hsc': "top1_simply_connected_on (top1_S2 - (D1 \<inter> D2))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2)))"
      using hsc by simp
    \<comment> \<open>By Theorem 63.3 contrapositive: since D = D1\<union>D2 separates,
       at least one of D1, D2 must separate S^2.\<close>
    have "top1_separates_on top1_S2 top1_S2_topology D1
        \<or> top1_separates_on top1_S2 top1_S2_topology D2"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence h1: "\<not> top1_separates_on top1_S2 top1_S2_topology D1"
          and h2: "\<not> top1_separates_on top1_S2 top1_S2_topology D2" by auto
      have "\<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
      proof (rule Theorem_63_3_general_nonseparation)
        show "is_topology_on_strict top1_S2 top1_S2_topology" by (rule assms(1))
        show "closedin_on top1_S2 top1_S2_topology D1" by (rule hD1_closed)
        show "closedin_on top1_S2 top1_S2_topology D2" by (rule hD2_closed)
        show "top1_simply_connected_on (top1_S2 - (D1 \<inter> D2))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2)))"
          by (rule hsc')
        show "\<not> top1_separates_on top1_S2 top1_S2_topology D1" by (rule h1)
        show "\<not> top1_separates_on top1_S2 top1_S2_topology D2" by (rule h2)
      qed
      thus False using hsep hD by simp
    qed
    \<comment> \<open>BY JOINING LEMMA CONTRAPOSITIVE: at least one of D1, D2 separates a' from b'.
       The joining lemma says: if a' joinable to b' in S^2-D1 AND S^2-D2, then in S^2-D.
       Contrapositive: if NOT joinable in S^2-D, then NOT joinable in S^2-D1 OR S^2-D2.\<close>

    \<comment> \<open>Get specific a', b' that D separates.\<close>
    obtain a' b' where ha': "a' \<in> top1_S2 - D" and hb': "b' \<in> top1_S2 - D"
        and hab'_sep: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - D)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a' b' f)"
    proof -
      have hTS2D: "is_topology_on (top1_S2 - D)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D))"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (by100 blast)
      have "\<exists>a b. a \<in> top1_S2 - D \<and> b \<in> top1_S2 - D \<and> \<not> (\<exists>f. top1_is_path_on
          (top1_S2 - D) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a b f)"
        by (rule not_connected_imp_no_path[OF hTS2D hsep[unfolded top1_separates_on_def]])
      thus ?thesis using that by (by100 blast)
    qed
    have ha'_S2: "a' \<in> top1_S2" using ha' by (by100 blast)
    have hb'_S2: "b' \<in> top1_S2" using hb' by (by100 blast)

    \<comment> \<open>Contrapositive of joining lemma: at least one half separates a' from b'.\<close>
    have hab'_D: "a' \<in> top1_S2 - (D1 \<union> D2)" "b' \<in> top1_S2 - (D1 \<union> D2)"
      using ha' hb' hD by auto
    have "\<not> (\<exists>f. top1_is_path_on (top1_S2 - D1)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a' b' f)
        \<or> \<not> (\<exists>f. top1_is_path_on (top1_S2 - D2)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) a' b' f)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence hab_D1: "\<exists>f. top1_is_path_on (top1_S2 - D1)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D1)) a' b' f"
        and hab_D2: "\<exists>f. top1_is_path_on (top1_S2 - D2)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D2)) a' b' f" by auto
      have "\<exists>f. top1_is_path_on (top1_S2 - (D1 \<union> D2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<union> D2))) a' b' f"
        by (rule arc_joining_lemma[OF assms(1) hD1_sub hD2_sub hD1_closed hD2_closed
            hD12 hd_S2 hab'_D hab_D1 hab_D2])
      hence "\<exists>f. top1_is_path_on (top1_S2 - D)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D)) a' b' f"
        using hD by simp
      thus False using hab'_sep by contradiction
    qed

    \<comment> \<open>BISECTION ITERATION + LIMIT ARGUMENT:
       At each step, pick the half that separates a' from b'. Both halves are arcs
       (from arc_split_at_midpoint). Repeat to get nested arcs D \<supset> D^1 \<supset> D^2 \<supset> ...,
       each separating a' from b', with parametric length \<rightarrow> 0.
       The homeomorphism h0: [0,1] \<rightarrow> D maps nested sub-intervals to nested sub-arcs.
       By Cantor's intersection theorem: the intervals converge to a single point x.
       S^2-{h0(x)} is path-connected (simply connected). Path \<gamma>: a'\<rightarrow>b' in S^2-{h0(x)}.
       \<gamma>(I) compact, disjoint from {h0(x)} \<Rightarrow> dist(\<gamma>(I), h0(x)) > 0.
       h0 uniformly continuous on compact [0,1] \<Rightarrow> h0(sub-interval_n) \<subseteq> B(h0(x), \<epsilon>) for large n.
       So \<gamma> is a path from a' to b' in S^2 - D^n (since \<gamma>(I) \<inter> D^n = {}).
       But a', b' \<in> S^2 - D \<subseteq> S^2 - D^n. Contradiction with D^n separating a' from b'.\<close>
    \<comment> \<open>Step 1: Get homeomorphism h0: [0,1] \<rightarrow> D (standard topology).\<close>
    obtain h0 where hh0: "top1_homeomorphism_on I_set I_top D
        (subspace_topology top1_S2 top1_S2_topology D) h0"
      using assms(3) unfolding top1_is_arc_on_def by (by100 blast)
    have hh0_bij: "bij_betw h0 I_set D"
      using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
    have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
      by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
    have hh0_inj: "inj_on h0 {0..1::real}"
      using hh0_bij hI01 unfolding bij_betw_def by simp
    have hh0_img: "h0 ` {0..1} = D"
      using hh0_bij hI01 unfolding bij_betw_def by simp
    have hh0_cont_custom: "top1_continuous_map_on I_set I_top D
        (subspace_topology top1_S2 top1_S2_topology D) h0"
      using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
    have hh0_cont_std: "continuous_on {0..1::real} h0"
      unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix B :: "(real \<times> real \<times> real) set" assume "open B"
      \<comment> \<open>B is standard-open in R^3. B \<inter> D is open in D (subspace from S^2 subspace from R^3).
         h0\<inverse>(B \<inter> D) is open in I_set (from custom continuity).
         The I_set custom topology = standard [0,1] subspace topology.\<close>
      have "B \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using \<open>open B\<close> unfolding top1_open_sets_def by simp
      have hR3eq: "top1_S2_topology = subspace_topology UNIV
          (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2"
        unfolding top1_S2_topology_def
        using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
              product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
      have hD_sub_S2: "D \<subseteq> top1_S2" using assms(2) by (by100 blast)
      have "B \<inter> D \<in> subspace_topology top1_S2 top1_S2_topology D"
      proof -
        have "B \<inter> top1_S2 \<in> top1_S2_topology"
          using \<open>B \<in> top1_open_sets\<close> hR3eq unfolding subspace_topology_def by (by100 blast)
        moreover have "B \<inter> D = D \<inter> (B \<inter> top1_S2)" using hD_sub_S2 by (by100 blast)
        ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
      qed
      hence "{s \<in> I_set. h0 s \<in> B \<inter> D} \<in> I_top"
        using hh0_cont_custom unfolding top1_continuous_map_on_def by (by100 blast)
      have hh0_range: "\<forall>s \<in> I_set. h0 s \<in> D"
        using hh0_cont_custom unfolding top1_continuous_map_on_def by (by100 blast)
      hence "{s \<in> I_set. h0 s \<in> B} = {s \<in> I_set. h0 s \<in> B \<inter> D}" by (by100 blast)
      hence hpre_Itop: "{s \<in> I_set. h0 s \<in> B} \<in> I_top"
        using \<open>{s \<in> I_set. h0 s \<in> B \<inter> D} \<in> I_top\<close> by simp
      \<comment> \<open>I_top = subspace_topology UNIV top1_open_sets I_set.
         An I_top-open set = I_set \<inter> W for some standard-open W.\<close>
      obtain W where "W \<in> (top1_open_sets :: real set set)" "{s \<in> I_set. h0 s \<in> B} = I_set \<inter> W"
        using hpre_Itop unfolding top1_unit_interval_topology_def subspace_topology_def
        by (by100 blast)
      have hW_open: "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
      have hpre_W: "{s \<in> I_set. h0 s \<in> B} = I_set \<inter> W"
        by (rule \<open>{s \<in> I_set. h0 s \<in> B} = I_set \<inter> W\<close>)
      have "h0 -` B \<inter> {0..1} = {s \<in> I_set. h0 s \<in> B}" unfolding hI01 by (by100 blast)
      hence "h0 -` B \<inter> {0..1} = I_set \<inter> W" using hpre_W by simp
      hence "W \<inter> {0..1} = h0 -` B \<inter> {0..1::real}" unfolding hI01 by (by100 blast)
      thus "\<exists>T. open T \<and> T \<inter> {0..1} = h0 -` B \<inter> {0..1::real}"
        using hW_open by (by100 blast)
    qed
    \<comment> \<open>Step 2: Sequence of nested intervals. Use nat recursion.\<close>
    define pick_half :: "(real \<times> real) \<Rightarrow> (real \<times> real)" where
      "pick_half = (\<lambda>(lo, hi). let mid = (lo + hi) / 2 in
        if \<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {lo..mid})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {lo..mid})) a' b' f)
        then (lo, mid) else (mid, hi))"
    define seq :: "nat \<Rightarrow> real \<times> real" where
      "seq = rec_nat (0, 1) (\<lambda>_ iv. pick_half iv)"
    \<comment> \<open>Properties: nested, length \<rightarrow> 0, each h0(interval) separates a' from b'.\<close>
    have hseq_0: "seq 0 = (0, 1)" unfolding seq_def by simp
    have hseq_Suc: "\<And>n. seq (Suc n) = pick_half (seq n)" unfolding seq_def by simp
    have hpick_half_props: "\<And>lo hi. let mid = (lo + hi) / 2 in
        fst (pick_half (lo, hi)) = lo \<and> snd (pick_half (lo, hi)) = mid \<or>
        fst (pick_half (lo, hi)) = mid \<and> snd (pick_half (lo, hi)) = hi"
      unfolding pick_half_def by (simp add: Let_def)
    have hseq_len: "\<forall>n. snd (seq n) - fst (seq n) = (1/2)^n"
    proof (rule allI)
      fix n show "snd (seq n) - fst (seq n) = (1/2)^n"
      proof (induction n)
        case 0 show ?case using hseq_0 by simp
      next
        case (Suc n)
        have "seq (Suc n) = pick_half (seq n)" by (rule hseq_Suc)
        obtain lo hi where hlh: "seq n = (lo, hi)" by (cases "seq n")
        hence hlen: "hi - lo = (1/2)^n" using Suc by simp
        have hmid: "(lo + hi) / 2 - lo = (hi - lo) / 2" "hi - (lo + hi) / 2 = (hi - lo) / 2"
          by (simp_all add: field_simps)
        from hpick_half_props[of lo hi] hlh
        have "fst (pick_half (lo, hi)) = lo \<and> snd (pick_half (lo, hi)) = (lo+hi)/2 \<or>
            fst (pick_half (lo, hi)) = (lo+hi)/2 \<and> snd (pick_half (lo, hi)) = hi"
          by (simp add: Let_def)
        hence "snd (seq (Suc n)) - fst (seq (Suc n)) = (hi - lo) / 2"
          using \<open>seq (Suc n) = pick_half (seq n)\<close> hlh hmid by auto
        thus ?case using hlen by simp
      qed
    qed
    have hseq_nested: "\<forall>n. fst (seq n) \<le> fst (seq (Suc n)) \<and> snd (seq (Suc n)) \<le> snd (seq n)"
    proof (rule allI, intro conjI)
      fix n
      obtain lo hi where hlh: "seq n = (lo, hi)" by (cases "seq n")
      have hlen_pos: "hi - lo = (1/2)^n"
        using spec[OF hseq_len, of n] hlh by simp
      hence "lo \<le> hi" by (simp add: algebra_simps)
      hence hmid_range: "lo \<le> (lo+hi)/2" "(lo+hi)/2 \<le> hi" by auto
      note hph = hpick_half_props[of lo hi]
      have hcases: "fst (pick_half (lo, hi)) = lo \<and> snd (pick_half (lo, hi)) = (lo+hi)/2 \<or>
          fst (pick_half (lo, hi)) = (lo+hi)/2 \<and> snd (pick_half (lo, hi)) = hi"
        using hph by (simp add: Let_def)
      show "fst (seq n) \<le> fst (seq (Suc n))"
        using hcases hseq_Suc hlh hmid_range by auto
      show "snd (seq (Suc n)) \<le> snd (seq n)"
        using hcases hseq_Suc hlh hmid_range by auto
    qed
    have hseq_range: "\<forall>n. 0 \<le> fst (seq n) \<and> snd (seq n) \<le> 1"
    proof (rule allI)
      fix n show "0 \<le> fst (seq n) \<and> snd (seq n) \<le> 1"
      proof (induction n)
        case 0 show ?case using hseq_0 by simp
      next
        case (Suc n)
        have "fst (seq n) \<le> fst (seq (Suc n))" using hseq_nested by (by100 blast)
        moreover have "snd (seq (Suc n)) \<le> snd (seq n)" using hseq_nested by (by100 blast)
        ultimately show ?case using Suc by simp
      qed
    qed
    have hseq_sep: "\<forall>n. \<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {fst (seq n)..snd (seq n)})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq n)..snd (seq n)}))
        a' b' f)"
    proof (rule allI)
      fix n show "\<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {fst (seq n)..snd (seq n)})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq n)..snd (seq n)}))
          a' b' f)"
      proof (induction n)
        case 0
        have "h0 ` {fst (seq 0)..snd (seq 0)} = D"
          using hseq_0 hh0_img by simp
        thus ?case using hab'_sep by simp
      next
        case (Suc n)
        \<comment> \<open>IH: can't be joined in S^2-h0(I_n). pick_half picks the bad half.\<close>
        obtain lo hi where hlh: "seq n = (lo, hi)" by (cases "seq n")
        let ?mid = "(lo + hi) / 2"
        have "seq (Suc n) = pick_half (lo, hi)" using hseq_Suc hlh by simp
        show ?case
        proof (cases "\<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {lo..?mid})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {lo..?mid})) a' b' f)")
          case True
          \<comment> \<open>pick_half picks left half (lo, mid).\<close>
          have hph_True: "pick_half (lo, hi) = (lo, ?mid)"
            unfolding pick_half_def Let_def using True by simp
          hence "seq (Suc n) = (lo, ?mid)" using \<open>seq (Suc n) = pick_half (lo, hi)\<close> by simp
          hence "h0 ` {fst (seq (Suc n))..snd (seq (Suc n))} = h0 ` {lo..?mid}" by simp
          thus ?thesis using True by simp
        next
          case False
          hence hjoinable_left: "\<exists>f. top1_is_path_on (top1_S2 - h0 ` {lo..?mid})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {lo..?mid})) a' b' f"
            by simp
          have hph_False: "pick_half (lo, hi) = (?mid, hi)"
            unfolding pick_half_def Let_def using False by auto
          hence hseq_eq: "seq (Suc n) = (?mid, hi)" using \<open>seq (Suc n) = pick_half (lo, hi)\<close> by simp
          \<comment> \<open>By joining lemma contrapositive: since can't join in S^2-h0({lo..hi}),
             and CAN join in S^2-h0({lo..mid}), MUST NOT join in S^2-h0({mid..hi}).\<close>
          have hcant_join_right: "\<not> (\<exists>f. top1_is_path_on (top1_S2 - h0 ` {?mid..hi})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {?mid..hi})) a' b' f)"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence hjoinable_right: "\<exists>f. top1_is_path_on (top1_S2 - h0 ` {?mid..hi})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {?mid..hi})) a' b' f"
              by simp
            \<comment> \<open>Both halves joinable. By arc_joining_lemma, full arc joinable. Contradiction.\<close>
            \<comment> \<open>Need: h0({lo..mid}) and h0({mid..hi}) are arcs, closed, intersect in {h0(mid)}.\<close>
            \<comment> \<open>a', b' \<in> S^2 - D \<subseteq> S^2 - h0({lo..hi}).\<close>
            \<comment> \<open>Setup for arc_joining_lemma.\<close>
            let ?D1 = "h0 ` {lo..?mid}" and ?D2 = "h0 ` {?mid..hi}"
            have hlen_n: "hi - lo = (1/2)^n"
              using spec[OF hseq_len, of n] hlh by simp
            hence "lo \<le> hi" by (simp add: algebra_simps)
            hence hmid_range: "lo \<le> ?mid" "?mid \<le> hi" by auto
            have hD1_sub: "?D1 \<subseteq> top1_S2"
            proof -
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "?mid \<le> 1" using \<open>hi \<le> 1\<close> hmid_range by linarith
              have "{lo..?mid} \<subseteq> {0..1}" using \<open>0 \<le> lo\<close> \<open>?mid \<le> 1\<close> by auto
              hence "h0 ` {lo..?mid} \<subseteq> D" using hh0_img by (by100 blast)
              thus ?thesis using assms(2) by (by100 blast)
            qed
            have hD2_sub: "?D2 \<subseteq> top1_S2"
            proof -
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "0 \<le> ?mid" using \<open>0 \<le> lo\<close> hmid_range by linarith
              have "{?mid..hi} \<subseteq> {0..1}" using \<open>0 \<le> ?mid\<close> \<open>hi \<le> 1\<close> by auto
              hence "h0 ` {?mid..hi} \<subseteq> D" using hh0_img by (by100 blast)
              thus ?thesis using assms(2) by (by100 blast)
            qed
            have hD1_closed: "closedin_on top1_S2 top1_S2_topology ?D1"
            proof -
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "{lo..?mid} \<subseteq> {0..1}" using \<open>0 \<le> lo\<close> hmid_range \<open>hi \<le> 1\<close> by auto
              have "continuous_on {lo..?mid} h0"
                by (rule continuous_on_subset[OF hh0_cont_std \<open>{lo..?mid} \<subseteq> {0..1}\<close>])
              have "compact {lo..?mid}" by (rule compact_Icc)
              hence "compact (h0 ` {lo..?mid})"
                by (rule compact_continuous_image[OF \<open>continuous_on {lo..?mid} h0\<close>])
              hence "closed (h0 ` {lo..?mid})" by (rule compact_imp_closed)
              \<comment> \<open>closed in R^3 + subset of S^2 → closedin_on S^2.\<close>
              show ?thesis unfolding closedin_on_def
              proof (intro conjI)
                show "?D1 \<subseteq> top1_S2" by (rule hD1_sub)
                show "top1_S2 - ?D1 \<in> top1_S2_topology"
                proof -
                  have "open (- h0 ` {lo..?mid})" using \<open>closed (h0 ` {lo..?mid})\<close>
                    by (rule open_Compl)
                  have hR3eq: "top1_S2_topology = subspace_topology UNIV
                      (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                    unfolding top1_S2_topology_def
                    using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                          product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
                  have "- h0 ` {lo..?mid} \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                    using \<open>open (- h0 ` {lo..?mid})\<close> unfolding top1_open_sets_def by simp
                  have "top1_S2 \<inter> (- h0 ` {lo..?mid}) \<in> top1_S2_topology"
                    using \<open>- h0 ` {lo..?mid} \<in> top1_open_sets\<close> hR3eq
                    unfolding subspace_topology_def by (by100 blast)
                  moreover have "top1_S2 - ?D1 = top1_S2 \<inter> (- h0 ` {lo..?mid})" by (by100 blast)
                  ultimately show ?thesis by simp
                qed
              qed
            qed
            have hD2_closed: "closedin_on top1_S2 top1_S2_topology ?D2"
            proof -
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "{?mid..hi} \<subseteq> {0..1}" using \<open>0 \<le> lo\<close> hmid_range \<open>hi \<le> 1\<close> by auto
              have "continuous_on {?mid..hi} h0"
                by (rule continuous_on_subset[OF hh0_cont_std \<open>{?mid..hi} \<subseteq> {0..1}\<close>])
              have "compact {?mid..hi}" by (rule compact_Icc)
              hence "compact (h0 ` {?mid..hi})"
                by (rule compact_continuous_image[OF \<open>continuous_on {?mid..hi} h0\<close>])
              hence "closed (h0 ` {?mid..hi})" by (rule compact_imp_closed)
              show ?thesis unfolding closedin_on_def
              proof (intro conjI)
                show "?D2 \<subseteq> top1_S2" by (rule hD2_sub)
                show "top1_S2 - ?D2 \<in> top1_S2_topology"
                proof -
                  have "open (- h0 ` {?mid..hi})" using \<open>closed (h0 ` {?mid..hi})\<close>
                    by (rule open_Compl)
                  have hR3eq: "top1_S2_topology = subspace_topology UNIV
                      (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                    unfolding top1_S2_topology_def
                    using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                          product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
                  have "- h0 ` {?mid..hi} \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                    using \<open>open (- h0 ` {?mid..hi})\<close> unfolding top1_open_sets_def by simp
                  have "top1_S2 \<inter> (- h0 ` {?mid..hi}) \<in> top1_S2_topology"
                    using \<open>- h0 ` {?mid..hi} \<in> top1_open_sets\<close> hR3eq
                    unfolding subspace_topology_def by (by100 blast)
                  moreover have "top1_S2 - ?D2 = top1_S2 \<inter> (- h0 ` {?mid..hi})" by (by100 blast)
                  ultimately show ?thesis by simp
                qed
              qed
            qed
            have hD12_inter: "?D1 \<inter> ?D2 = {h0 ?mid}"
            proof (rule set_eqI, rule iffI)
              fix y assume "y \<in> ?D1 \<inter> ?D2"
              then obtain s t where hs: "s \<in> {lo..?mid}" "y = h0 s"
                  and ht: "t \<in> {?mid..hi}" "y = h0 t" by (by100 blast)
              hence "h0 s = h0 t" by simp
              have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
              have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
              have "s \<in> {0..1}" using hs(1) \<open>0 \<le> lo\<close> hmid_range \<open>hi \<le> 1\<close> by auto
              have "t \<in> {0..1}" using ht(1) \<open>0 \<le> lo\<close> hmid_range \<open>hi \<le> 1\<close> by auto
              have "s = t" using \<open>h0 s = h0 t\<close> hh0_inj \<open>s \<in> {0..1}\<close> \<open>t \<in> {0..1}\<close>
                unfolding inj_on_def by (by100 blast)
              have "s \<le> ?mid" using hs(1) by simp
              have "?mid \<le> s" using ht(1) \<open>s = t\<close> by simp
              hence "s = ?mid" using \<open>s \<le> ?mid\<close> by linarith
              have "y = h0 ?mid" using hs(2) \<open>s = ?mid\<close> by simp
              thus "y \<in> {h0 ?mid}" by simp
            next
              fix y assume "y \<in> {h0 ?mid}"
              hence "y = h0 ?mid" by simp
              moreover have "?mid \<in> {lo..?mid}" "?mid \<in> {?mid..hi}" using hmid_range by auto
              ultimately show "y \<in> ?D1 \<inter> ?D2" by (by100 blast)
            qed
            have hd_S2: "h0 ?mid \<in> top1_S2"
            proof -
              have "?mid \<in> {lo..?mid}" using hmid_range by simp
              hence "h0 ?mid \<in> ?D1" by (by100 blast)
              thus ?thesis using hD1_sub by (by100 blast)
            qed
            have hD12_union: "?D1 \<union> ?D2 = h0 ` {lo..hi}"
              using hmid_range by (auto simp: image_Un[symmetric] ivl_disj_un_two_touch)
            have hab'_D12: "a' \<in> top1_S2 - (?D1 \<union> ?D2)" "b' \<in> top1_S2 - (?D1 \<union> ?D2)"
            proof -
              have "h0 ` {lo..hi} \<subseteq> D"
              proof -
                have "0 \<le> lo" using spec[OF hseq_range, of n] hlh by simp
                have "hi \<le> 1" using spec[OF hseq_range, of n] hlh by simp
                have "{lo..hi} \<subseteq> {0..1}" using \<open>0 \<le> lo\<close> \<open>hi \<le> 1\<close> by auto
                thus ?thesis using hh0_img by (by100 blast)
              qed
              hence "?D1 \<union> ?D2 \<subseteq> D" using hD12_union by simp
              thus "a' \<in> top1_S2 - (?D1 \<union> ?D2)" "b' \<in> top1_S2 - (?D1 \<union> ?D2)"
                using ha' hb' by (by100 blast)+
            qed
            have "\<exists>f. top1_is_path_on (top1_S2 - h0 ` {lo..hi})
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {lo..hi})) a' b' f"
            proof -
              have "?D1 \<union> ?D2 = h0 ` {lo..hi}"
                using hmid_range by (auto simp: image_Un[symmetric] ivl_disj_un_two_touch)
              have "\<exists>f. top1_is_path_on (top1_S2 - (?D1 \<union> ?D2))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?D1 \<union> ?D2))) a' b' f"
                by (rule arc_joining_lemma[OF assms(1) hD1_sub hD2_sub hD1_closed hD2_closed
                    hD12_inter hd_S2 hab'_D12 hjoinable_left hjoinable_right])
              thus ?thesis using \<open>?D1 \<union> ?D2 = h0 ` {lo..hi}\<close> by simp
            qed
            moreover have "h0 ` {fst (seq n)..snd (seq n)} = h0 ` {lo..hi}" using hlh by simp
            ultimately show False using Suc by simp
          qed
          have "h0 ` {fst (seq (Suc n))..snd (seq (Suc n))} = h0 ` {?mid..hi}"
            using hseq_eq by simp
          thus ?thesis using hcant_join_right by simp
        qed
      qed
    qed
    \<comment> \<open>Step 3: Cantor intersection. Monotone bounded sequences converge.\<close>
    define x where "x = (SUP n. fst (seq n))"
    have hfst_le_snd: "\<forall>n. fst (seq n) \<le> snd (seq n)"
    proof
      fix n have "snd (seq n) - fst (seq n) = (1/2)^n" using hseq_len by (by100 blast)
      moreover have "(1/2::real)^n \<ge> 0" by simp
      ultimately show "fst (seq n) \<le> snd (seq n)" by linarith
    qed
    have hfst_le_1: "\<forall>n. fst (seq n) \<le> 1"
    proof
      fix n show "fst (seq n) \<le> 1"
        using spec[OF hfst_le_snd, of n] spec[OF hseq_range, of n] by linarith
    qed
    have hbdd: "bdd_above (range (\<lambda>n. fst (seq n)))"
      by (intro bdd_aboveI[of _ 1]) (use hfst_le_1 in auto)
    have hx_range: "0 \<le> x \<and> x \<le> 1"
    proof (intro conjI)
      show "0 \<le> x"
      proof -
        have "fst (seq 0) \<in> range (\<lambda>n. fst (seq n))" by (by100 blast)
        hence "fst (seq 0) \<le> x" unfolding x_def
          using cSUP_upper[OF _ hbdd] by (by100 blast)
        thus ?thesis using hseq_0 by simp
      qed
      show "x \<le> 1"
      proof -
        have "\<forall>n. fst (seq n) \<le> 1" by (rule hfst_le_1)
        hence "Sup (range (\<lambda>n. fst (seq n))) \<le> 1"
          by (intro cSup_least) auto
        thus ?thesis unfolding x_def by simp
      qed
    qed
    have hx_ge_fst: "\<forall>n. fst (seq n) \<le> x"
    proof
      fix n
      have "fst (seq n) \<in> range (\<lambda>n. fst (seq n))" by (by100 blast)
      thus "fst (seq n) \<le> x" unfolding x_def using cSUP_upper[OF _ hbdd] by (by100 blast)
    qed
    have hx_le_snd: "\<forall>n. x \<le> snd (seq n)"
    proof
      fix n
      have "\<forall>m. fst (seq m) \<le> snd (seq n)"
      proof
        fix m show "fst (seq m) \<le> snd (seq n)"
        proof (cases "m \<le> n")
          case True
          have "fst (seq m) \<le> fst (seq n)"
            by (rule lift_Suc_mono_le[of "\<lambda>k. fst (seq k)"])
               (use hseq_nested in auto, rule True)
          also have "... \<le> snd (seq n)" using hfst_le_snd by (by100 blast)
          finally show ?thesis .
        next
          case False hence "n \<le> m" by simp
          have "snd (seq m) \<le> snd (seq n)"
            using \<open>n \<le> m\<close>
          proof (induction m)
            case 0 thus ?case by simp
          next
            case (Suc m)
            show ?case
            proof (cases "n \<le> m")
              case True
              have "snd (seq (Suc m)) \<le> snd (seq m)" using hseq_nested by (by100 blast)
              also have "... \<le> snd (seq n)" using Suc True by simp
              finally show ?thesis .
            next
              case False hence "n = Suc m" using Suc by simp
              thus ?thesis by simp
            qed
          qed
          have "fst (seq m) \<le> snd (seq m)" using hfst_le_snd by (by100 blast)
          thus ?thesis using \<open>snd (seq m) \<le> snd (seq n)\<close> by linarith
        qed
      qed
      thus "x \<le> snd (seq n)" unfolding x_def
        using cSup_least[of "range (\<lambda>m. fst (seq m))"] by auto
    qed
    have hx_limit: "\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. fst (seq n) \<le> x \<and> x \<le> snd (seq n) \<and>
        snd (seq n) - fst (seq n) < \<epsilon>"
    proof (intro allI impI)
      fix \<epsilon> :: real assume "0 < \<epsilon>"
      obtain N where "(1/2::real)^N < \<epsilon>"
        using real_arch_pow_inv[OF \<open>0 < \<epsilon>\<close>, of "1/2"] by auto
      show "\<exists>N. \<forall>n\<ge>N. fst (seq n) \<le> x \<and> x \<le> snd (seq n) \<and> snd (seq n) - fst (seq n) < \<epsilon>"
      proof (intro exI[of _ N] allI impI)
        fix n assume "N \<le> n"
        show "fst (seq n) \<le> x \<and> x \<le> snd (seq n) \<and> snd (seq n) - fst (seq n) < \<epsilon>"
        proof (intro conjI)
          show "fst (seq n) \<le> x" using hx_ge_fst by (by100 blast)
          show "x \<le> snd (seq n)" using hx_le_snd by (by100 blast)
          have "snd (seq n) - fst (seq n) = (1/2)^n" using hseq_len by (by100 blast)
          also have "... \<le> (1/2::real)^N" using \<open>N \<le> n\<close> by (rule power_decreasing) simp_all
          also have "... < \<epsilon>" by (rule \<open>(1/2)^N < \<epsilon>\<close>)
          finally show "snd (seq n) - fst (seq n) < \<epsilon>" .
        qed
      qed
    qed
    \<comment> \<open>Step 4: Path from a' to b' in S^2-{h0(x)}.\<close>
    have hx_S2: "h0 x \<in> top1_S2"
    proof -
      have "x \<in> {0..1}" using hx_range by simp
      hence "h0 x \<in> h0 ` {0..1}" by (by100 blast)
      hence "h0 x \<in> D" using hh0_img by simp
      thus ?thesis using assms(2) by (by100 blast)
    qed
    \<comment> \<open>Get custom path from S2_minus_point_simply_connected.\<close>
    have hh0x_in_D: "h0 x \<in> D"
    proof -
      have "x \<in> {0..1}" using hx_range by simp
      thus ?thesis using hh0_img by (by100 blast)
    qed
    have ha'_S2x: "a' \<in> top1_S2 - {h0 x}"
      using ha' hh0x_in_D by (by100 blast)
    have hb'_S2x: "b' \<in> top1_S2 - {h0 x}"
      using hb' hh0x_in_D by (by100 blast)
    have hpc_S2x: "top1_path_connected_on (top1_S2 - {h0 x})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x}))"
    proof -
      have "top1_simply_connected_on (top1_S2 - {h0 x})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x}))"
        by (rule S2_minus_point_simply_connected[OF hx_S2])
      thus ?thesis unfolding top1_simply_connected_on_def by (by100 blast)
    qed
    obtain \<alpha>_custom where h\<alpha>c: "top1_is_path_on (top1_S2 - {h0 x})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x})) a' b' \<alpha>_custom"
      using hpc_S2x ha'_S2x hb'_S2x unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>Bridge custom path to standard continuous_on.\<close>
    \<comment> \<open>Bridge custom path to standard continuous_on. Same pattern as h0_cont_std.\<close>
    have h\<alpha>c_cont: "top1_continuous_map_on I_set I_top (top1_S2 - {h0 x})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x})) \<alpha>_custom"
      using h\<alpha>c unfolding top1_is_path_on_def by (by100 blast)
    have h\<alpha>c_range: "\<forall>t\<in>I_set. \<alpha>_custom t \<in> top1_S2 - {h0 x}"
      using h\<alpha>c_cont unfolding top1_continuous_map_on_def by (by100 blast)
    have h\<alpha>c_0: "\<alpha>_custom 0 = a'" using h\<alpha>c unfolding top1_is_path_on_def by (by100 blast)
    have h\<alpha>c_1: "\<alpha>_custom 1 = b'" using h\<alpha>c unfolding top1_is_path_on_def by (by100 blast)
    have h\<alpha>c_cont_std: "continuous_on {0..1::real} \<alpha>_custom"
      unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix B :: "(real \<times> real \<times> real) set" assume "open B"
      have "B \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using \<open>open B\<close> unfolding top1_open_sets_def by simp
      have hR3eq: "top1_S2_topology = subspace_topology UNIV
          (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
        unfolding top1_S2_topology_def
        using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
              product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
      have hS2x_sub: "top1_S2 - {h0 x} \<subseteq> top1_S2" by (by100 blast)
      have "B \<inter> (top1_S2 - {h0 x}) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {h0 x})"
      proof -
        have "B \<inter> top1_S2 \<in> top1_S2_topology"
          using \<open>B \<in> top1_open_sets\<close> hR3eq unfolding subspace_topology_def by (by100 blast)
        moreover have "B \<inter> (top1_S2 - {h0 x}) = (top1_S2 - {h0 x}) \<inter> (B \<inter> top1_S2)"
          by (by100 blast)
        ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
      qed
      hence "{s \<in> I_set. \<alpha>_custom s \<in> B \<inter> (top1_S2 - {h0 x})} \<in> I_top"
        using h\<alpha>c_cont unfolding top1_continuous_map_on_def by (by100 blast)
      have "{s \<in> I_set. \<alpha>_custom s \<in> B} = {s \<in> I_set. \<alpha>_custom s \<in> B \<inter> (top1_S2 - {h0 x})}"
        using h\<alpha>c_range by (by100 blast)
      hence "{s \<in> I_set. \<alpha>_custom s \<in> B} \<in> I_top"
        using \<open>{s \<in> I_set. \<alpha>_custom s \<in> B \<inter> _} \<in> I_top\<close> by simp
      then obtain W where "W \<in> (top1_open_sets :: real set set)"
          "{s \<in> I_set. \<alpha>_custom s \<in> B} = I_set \<inter> W"
        unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
      have "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
      have "\<alpha>_custom -` B \<inter> {0..1} = {s \<in> I_set. \<alpha>_custom s \<in> B}" unfolding hI01 by (by100 blast)
      hence "\<alpha>_custom -` B \<inter> {0..1} = I_set \<inter> W"
        using \<open>{s \<in> I_set. \<alpha>_custom s \<in> B} = I_set \<inter> W\<close> by simp
      hence "W \<inter> {0..1} = \<alpha>_custom -` B \<inter> {0..1}" unfolding hI01 by (by100 blast)
      thus "\<exists>T. open T \<and> T \<inter> {0..1} = \<alpha>_custom -` B \<inter> {0..1::real}"
        using \<open>open W\<close> by (by100 blast)
    qed
    define \<alpha> where "\<alpha> = \<alpha>_custom"
    have h\<alpha>: "continuous_on {0..1::real} \<alpha>"
        "\<alpha> 0 = a'" "\<alpha> 1 = b'" "\<forall>t\<in>{0..1}. \<alpha> t \<in> top1_S2 - {h0 x}"
      unfolding \<alpha>_def using h\<alpha>c_cont_std h\<alpha>c_0 h\<alpha>c_1 h\<alpha>c_range unfolding hI01 by auto
    \<comment> \<open>Step 5: \<alpha>(I) compact, positive distance from h0(x).\<close>
    have h\<alpha>_compact: "compact (\<alpha> ` {0..1})" by (rule compact_continuous_image[OF h\<alpha>(1) compact_Icc])
    have h\<alpha>_disjoint: "h0 x \<notin> \<alpha> ` {0..1}"
    proof
      assume "h0 x \<in> \<alpha> ` {0..1}"
      then obtain t where "t \<in> {0..1}" "\<alpha> t = h0 x" by auto
      hence "\<alpha> t \<in> top1_S2 - {h0 x}" using h\<alpha>(4) \<open>t \<in> {0..1}\<close> by simp
      hence "\<alpha> t \<noteq> h0 x" by (by100 blast)
      thus False using \<open>\<alpha> t = h0 x\<close> by simp
    qed
    \<comment> \<open>Step 5: \<alpha>(I) compact hence closed. S^2-\<alpha>(I) open, contains h0(x).\<close>
    have h\<alpha>_closed: "closed (\<alpha> ` {0..1})" by (rule compact_imp_closed[OF h\<alpha>_compact])
    have hcompl_open: "open (- \<alpha> ` {0..1})" using h\<alpha>_closed by (rule open_Compl)
    have hh0x_in_compl: "h0 x \<in> - \<alpha> ` {0..1}" using h\<alpha>_disjoint by simp
    \<comment> \<open>Step 6: h0 continuous at x. Find open neighborhood of x whose h0-image avoids \<alpha>.\<close>
    have "\<exists>U. open U \<and> x \<in> U \<and> h0 ` (U \<inter> {0..1}) \<subseteq> - \<alpha> ` {0..1}"
    proof -
      have "open (- \<alpha> ` {0..1})" by (rule hcompl_open)
      moreover have "h0 x \<in> - \<alpha> ` {0..1}" by (rule hh0x_in_compl)
      \<comment> \<open>continuous_on_open_invariant: preimage of open is relatively open.\<close>
      obtain W where hW_open: "open W" and hW_eq: "W \<inter> {0..1} = h0 -` (- \<alpha> ` {0..1}) \<inter> {0..1}"
        using iffD1[OF continuous_on_open_invariant hh0_cont_std, rule_format, OF hcompl_open]
        by auto
      have "x \<in> W"
      proof -
        have "x \<in> h0 -` (- \<alpha> ` {0..1}) \<inter> {0..1}" using hh0x_in_compl hx_range by simp
        hence "x \<in> W \<inter> {0..1}" using hW_eq by auto
        thus "x \<in> W" by simp
      qed
      have "h0 ` (W \<inter> {0..1}) \<subseteq> - \<alpha> ` {0..1}"
      proof
        fix y assume "y \<in> h0 ` (W \<inter> {0..1})"
        then obtain t where "t \<in> W \<inter> {0..1}" "y = h0 t" by (by100 blast)
        hence "t \<in> h0 -` (- \<alpha> ` {0..1}) \<inter> {0..1}" using hW_eq by auto
        thus "y \<in> - \<alpha> ` {0..1}" using \<open>y = h0 t\<close> by simp
      qed
      thus ?thesis using hW_open \<open>x \<in> W\<close> by (by100 blast)
    qed
    then obtain U_nbhd where hU_open: "open U_nbhd" and hx_U: "x \<in> U_nbhd"
        and hU_avoids: "h0 ` (U_nbhd \<inter> {0..1}) \<subseteq> - \<alpha> ` {0..1}" by blast
    \<comment> \<open>For large m, I_m \<subseteq> U_nbhd (since I_m shrinks to {x} and U_nbhd is open).\<close>
    have "\<exists>N. {fst (seq N)..snd (seq N)} \<subseteq> U_nbhd \<inter> {0..1}"
    proof -
      obtain \<delta> where h\<delta>: "\<delta> > 0" "\<forall>y. dist y x < \<delta> \<longrightarrow> y \<in> U_nbhd"
        using hU_open hx_U unfolding open_dist by (by100 blast)
      obtain N where hN': "\<forall>n\<ge>N. fst (seq n) \<le> x \<and> x \<le> snd (seq n) \<and>
          snd (seq n) - fst (seq n) < \<delta>"
        using spec[OF hx_limit, of \<delta>] h\<delta>(1) by (by100 blast)
      have "{fst (seq N)..snd (seq N)} \<subseteq> U_nbhd \<inter> {0..1}"
      proof
        fix t assume "t \<in> {fst (seq N)..snd (seq N)}"
        hence ht: "fst (seq N) \<le> t" "t \<le> snd (seq N)" by auto
        have hN_props: "fst (seq N) \<le> x" "x \<le> snd (seq N)"
            "snd (seq N) - fst (seq N) < \<delta>"
          using hN' by auto
        have "dist t x < \<delta>"
          using ht hN_props unfolding dist_real_def by linarith
        hence "t \<in> U_nbhd" using h\<delta>(2) by simp
        moreover have "t \<in> {0..1}"
          using ht spec[OF hseq_range, of N] hfst_le_snd by auto
        ultimately show "t \<in> U_nbhd \<inter> {0..1}" by simp
      qed
      thus ?thesis by (by100 blast)
    qed
    then obtain N where hN_sub: "{fst (seq N)..snd (seq N)} \<subseteq> U_nbhd \<inter> {0..1}" by blast
    have hN: "h0 ` {fst (seq N)..snd (seq N)} \<subseteq> - \<alpha> ` {0..1}"
      using hN_sub hU_avoids by (by100 blast)
    have h\<alpha>_avoids: "\<alpha> ` {0..1} \<inter> h0 ` {fst (seq N)..snd (seq N)} = {}"
      using hN by (by100 blast)
    \<comment> \<open>\<alpha> is a path from a' to b' in S^2 - h0(I_N), contradicting separation.\<close>
    \<comment> \<open>\<alpha> maps into S^2-h0(I_N) (from h\<alpha>(4) + h\<alpha>_avoids).\<close>
    have h\<alpha>_in_DN: "\<forall>t\<in>I_set. \<alpha> t \<in> top1_S2 - h0 ` {fst (seq N)..snd (seq N)}"
    proof
      fix t assume "t \<in> I_set"
      hence "t \<in> {0..1::real}" unfolding hI01 by simp
      have "\<alpha> t \<in> top1_S2 - {h0 x}" using h\<alpha>(4) \<open>t \<in> {0..1}\<close> by simp
      hence h1: "\<alpha> t \<in> top1_S2" by (by100 blast)
      have h2: "\<alpha> t \<notin> h0 ` {fst (seq N)..snd (seq N)}"
      proof
        assume "\<alpha> t \<in> h0 ` {fst (seq N)..snd (seq N)}"
        hence "\<alpha> t \<in> \<alpha> ` {0..1} \<inter> h0 ` {fst (seq N)..snd (seq N)}"
          using \<open>t \<in> {0..1}\<close> by (by100 blast)
        thus False using h\<alpha>_avoids by (by100 blast)
      qed
      show "\<alpha> t \<in> top1_S2 - h0 ` {fst (seq N)..snd (seq N)}" using h1 h2 by (by100 blast)
    qed
    \<comment> \<open>Bridge standard \<alpha> to custom top1_is_path_on.\<close>
    have hpath_exists: "\<exists>f. top1_is_path_on (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq N)..snd (seq N)}))
        a' b' f"
    proof (intro exI[of _ \<alpha>])
      show "top1_is_path_on (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq N)..snd (seq N)}))
          a' b' \<alpha>"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top
            (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})) \<alpha>"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume "s \<in> I_set"
          thus "\<alpha> s \<in> top1_S2 - h0 ` {fst (seq N)..snd (seq N)}" using h\<alpha>_in_DN by simp
        next
          fix W assume "W \<in> subspace_topology top1_S2 top1_S2_topology
              (top1_S2 - h0 ` {fst (seq N)..snd (seq N)})"
          then obtain V where "V \<in> top1_S2_topology"
              "W = (top1_S2 - h0 ` {fst (seq N)..snd (seq N)}) \<inter> V"
            unfolding subspace_topology_def by (by100 blast)
          have hR3eq: "top1_S2_topology = subspace_topology UNIV
              (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
            unfolding top1_S2_topology_def
            using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                  product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
          obtain V' where hV': "V' \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
              "V = top1_S2 \<inter> V'"
            using \<open>V \<in> top1_S2_topology\<close> hR3eq
            unfolding subspace_topology_def by (by100 blast)
          have "open V'" using hV' unfolding top1_open_sets_def by simp
          have "{s \<in> I_set. \<alpha> s \<in> W} = {s \<in> I_set. \<alpha> s \<in> V'}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. \<alpha> s \<in> W}"
            thus "s \<in> {s \<in> I_set. \<alpha> s \<in> V'}"
              using \<open>W = _ \<inter> V\<close> \<open>V = _ \<inter> V'\<close> by (by100 blast)
          next
            fix s assume "s \<in> {s \<in> I_set. \<alpha> s \<in> V'}"
            hence "s \<in> I_set" "\<alpha> s \<in> V'" by auto
            have "\<alpha> s \<in> top1_S2 - h0 ` {fst (seq N)..snd (seq N)}"
              using h\<alpha>_in_DN \<open>s \<in> I_set\<close> by simp
            thus "s \<in> {s \<in> I_set. \<alpha> s \<in> W}"
              using \<open>W = _ \<inter> V\<close> \<open>V = _ \<inter> V'\<close> \<open>\<alpha> s \<in> V'\<close> \<open>s \<in> I_set\<close> by (by100 blast)
          qed
          moreover have "{s \<in> I_set. \<alpha> s \<in> V'} \<in> I_top"
          proof -
            obtain U_r where "open U_r" "\<alpha> -` V' \<inter> {0..1} = U_r \<inter> {0..1}"
              using iffD1[OF continuous_on_open_invariant h\<alpha>(1), rule_format, OF \<open>open V'\<close>] by auto
            have "{s \<in> I_set. \<alpha> s \<in> V'} = I_set \<inter> U_r" unfolding hI01
              using \<open>\<alpha> -` V' \<inter> {0..1} = U_r \<inter> {0..1}\<close> by (by100 blast)
            moreover have "U_r \<in> (top1_open_sets :: real set set)"
              using \<open>open U_r\<close> unfolding top1_open_sets_def by simp
            ultimately show ?thesis
              unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
          qed
          ultimately show "{s \<in> I_set. \<alpha> s \<in> W} \<in> I_top" by simp
        qed
        show "\<alpha> 0 = a'" by (rule h\<alpha>(2))
        show "\<alpha> 1 = b'" by (rule h\<alpha>(3))
      qed
    qed
    show False using hseq_sep hpath_exists by blast
  qed
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
  have hC_sep: "\<not> top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
  proof -
    \<comment> \<open>Step 1a: Get stereographic projection \<sigma>: S^2\{N} \<rightarrow> R^2.\<close>
    have hN_S2: "north_pole \<in> top1_S2" unfolding north_pole_def top1_S2_def by simp
    obtain \<sigma> where h\<sigma>: "top1_homeomorphism_on (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) \<sigma>"
      using S2_minus_point_homeo_R2[OF hN_S2] by (by100 blast)
    \<comment> \<open>Step 1b: Transfer C to S^2: C' = \<sigma>^{-1}(C) \<subseteq> S^2\{N}.\<close>
    define \<sigma>inv where "\<sigma>inv = inv_into (top1_S2 - {north_pole}) \<sigma>"
    define C' where "C' = \<sigma>inv ` C"
    have hC'_sub: "C' \<subseteq> top1_S2 - {north_pole}" unfolding C'_def \<sigma>inv_def
    proof
      fix x assume "x \<in> inv_into (top1_S2 - {north_pole}) \<sigma> ` C"
      then obtain c where hc: "c \<in> C" "x = inv_into (top1_S2 - {north_pole}) \<sigma> c" by (by100 blast)
      have hsurj: "\<sigma> ` (top1_S2 - {north_pole}) = UNIV"
        using h\<sigma> unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "c \<in> \<sigma> ` (top1_S2 - {north_pole})" using hsurj by simp
      hence "inv_into (top1_S2 - {north_pole}) \<sigma> c \<in> top1_S2 - {north_pole}"
        by (rule inv_into_into)
      thus "x \<in> top1_S2 - {north_pole}" using hc(2) by simp
    qed
    have hC'_sub_S2: "C' \<subseteq> top1_S2" using hC'_sub by (by100 blast)
    \<comment> \<open>Step 1c: C' is a simple closed curve on S^2.\<close>
    have hC'_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C'"
    proof -
      \<comment> \<open>From assumption: f: S^1 \<rightarrow> R^2 continuous injective with f(S^1) = C.\<close>
      obtain f where hf: "top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f"
          and hf_inj: "inj_on f top1_S1" and hf_img: "f ` top1_S1 = C"
        using assms unfolding top1_simple_closed_curve_on_def by (by100 blast)
      \<comment> \<open>\<sigma>^{-1}: R^2 \<rightarrow> S^2\{N} is the inverse of homeomorphism \<sigma>.\<close>
      have h\<sigma>inv_cont: "top1_continuous_map_on UNIV ?TR2
          (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>inv"
        using h\<sigma> unfolding top1_homeomorphism_on_def \<sigma>inv_def by (by100 blast)
      have h\<sigma>inv_inj: "inj_on \<sigma>inv UNIV"
      proof -
        have "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
          using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
        hence "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
          using \<sigma>inv_def by (simp add: bij_betw_inv_into)
        thus ?thesis unfolding bij_betw_def by (by100 blast)
      qed
      \<comment> \<open>g = \<sigma>^{-1} \<circ> f: S^1 \<rightarrow> S^2 continuous injective, g(S^1) = C'.\<close>
      define g where "g = \<sigma>inv \<circ> f"
      have hg_cont_S2N: "top1_continuous_map_on top1_S1 top1_S1_topology
          (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) g"
        unfolding g_def by (rule top1_continuous_map_on_comp[OF hf h\<sigma>inv_cont])
      \<comment> \<open>Lift to S^2: inclusion S^2\{N} \<hookrightarrow> S^2 is continuous.\<close>
      have hg_cont_S2: "top1_continuous_map_on top1_S1 top1_S1_topology
          top1_S2 top1_S2_topology g"
      proof -
        have "top1_continuous_map_on top1_S1 top1_S1_topology
            top1_S2 (subspace_topology top1_S2 top1_S2_topology top1_S2) g"
          by (rule top1_continuous_map_on_codomain_enlarge[OF hg_cont_S2N]) blast+
        moreover have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
          by (rule subspace_topology_self_carrier)
             (use top1_S2_is_topology_on_strict[unfolded is_topology_on_strict_def]
              in \<open>auto simp: is_topology_on_def\<close>)
        ultimately show ?thesis by simp
      qed
      have hg_inj: "inj_on g top1_S1"
        unfolding g_def comp_def
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> top1_S1" and hy: "y \<in> top1_S1"
            and heq: "\<sigma>inv (f x) = \<sigma>inv (f y)"
        have "f x \<in> UNIV" by simp
        have "f y \<in> UNIV" by simp
        have "f x = f y" using h\<sigma>inv_inj heq unfolding inj_on_def by (by100 blast)
        thus "x = y" using hf_inj hx hy unfolding inj_on_def by (by100 blast)
      qed
      have hg_img: "g ` top1_S1 = C'"
        unfolding g_def C'_def image_comp[symmetric] using hf_img by simp
      show ?thesis unfolding top1_simple_closed_curve_on_def
        using hg_cont_S2 hg_inj hg_img by (by100 blast)
    qed
    \<comment> \<open>Step 1d: By Theorem 61.3, S^2\C' is not connected.\<close>
    have hS2_C'_sep: "top1_separates_on top1_S2 top1_S2_topology C'"
      by (rule Theorem_61_3_JordanSeparation_S2[OF top1_S2_is_topology_on_strict hC'_scc])
    \<comment> \<open>Step 1e: Transfer non-connectivity back to R^2.
       S^2\C' = (S^2\{N}\C') \<union> {N}. \<sigma> maps S^2\{N}\C' homeo to R^2\C.
       S^2\C' not connected \<Rightarrow> R^2\C not connected (if R^2\C connected,
       \<sigma>^{-1}(R^2\C) connected, and adding {N} preserves connectivity since
       N is a limit point of \<sigma>^{-1}(R^2\C), giving S^2\C' connected \<Rightarrow> contradiction).\<close>
    \<comment> \<open>Contrapositive: if R^2\C connected, then S^2\C' connected (contradiction).
       S^2\C' = \<sigma>^{-1}(R^2\C) \<union> {N}. \<sigma>^{-1}(R^2\C) connected (homeo image).
       N \<in> closure(\<sigma>^{-1}(R^2\C)) (unbounded points map near N).
       Connected \<union> limit point = connected.\<close>
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence hR2C_conn: "top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        by simp
      \<comment> \<open>\<sigma>^{-1}(R^2\C) connected.\<close>
      have h\<sigma>inv_R2C_conn: "top1_connected_on (\<sigma>inv ` (UNIV - C))
          (subspace_topology top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C)))"
      proof -
        \<comment> \<open>\<sigma>inv continuous from R^2 to S^2\{N}. Restrict domain to UNIV-C.\<close>
        have h\<sigma>inv_cont: "top1_continuous_map_on UNIV ?TR2
            (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>inv"
          using h\<sigma> unfolding top1_homeomorphism_on_def \<sigma>inv_def by (by100 blast)
        have hTR2: "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
        have hTR2C: "is_topology_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
          by (rule subspace_topology_is_topology_on[OF hTR2]) simp
        have h\<sigma>inv_cont_UC: "top1_continuous_map_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))
            (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) \<sigma>inv"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF h\<sigma>inv_cont]) simp
        have hTS2N: "is_topology_on (top1_S2 - {north_pole})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
        proof -
          have hTS2: "is_topology_on top1_S2 top1_S2_topology"
            using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          show ?thesis by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
        qed
        \<comment> \<open>By Theorem_23_5: \<sigma>inv(UNIV-C) connected in subspace of S^2\{N}.\<close>
        have "top1_connected_on (\<sigma>inv ` (UNIV - C))
            (subspace_topology (top1_S2 - {north_pole})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
              (\<sigma>inv ` (UNIV - C)))"
          by (rule Theorem_23_5[OF hTR2C hTS2N hR2C_conn h\<sigma>inv_cont_UC])
        \<comment> \<open>Bridge: subspace of S^2\{N} = subspace of S^2 (transitivity).\<close>
        moreover have "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - {north_pole}"
        proof -
          have hbij_\<sigma>: "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
            using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
          have "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
            unfolding \<sigma>inv_def by (rule bij_betw_inv_into[OF hbij_\<sigma>])
          thus ?thesis unfolding bij_betw_def by (by100 blast)
        qed
        moreover have "subspace_topology (top1_S2 - {north_pole})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
            (\<sigma>inv ` (UNIV - C))
            = subspace_topology top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
          by (rule subspace_topology_trans) (use \<open>\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - {north_pole}\<close> in blast)
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>S^2\C' = \<sigma>^{-1}(R^2\C) \<union> {N}.\<close>
      have hS2C'_eq: "top1_S2 - C' = \<sigma>inv ` (UNIV - C) \<union> {north_pole}"
      proof -
        have hbij: "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
          using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
        have hsurj: "\<sigma> ` (top1_S2 - {north_pole}) = UNIV"
          using hbij unfolding bij_betw_def by (by100 blast)
        have hinj: "inj_on \<sigma> (top1_S2 - {north_pole})"
          using hbij unfolding bij_betw_def by (by100 blast)
        have hbij_inv: "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
          unfolding \<sigma>inv_def by (rule bij_betw_inv_into[OF hbij])
        have h\<sigma>inv_img: "\<sigma>inv ` UNIV = top1_S2 - {north_pole}"
          using hbij_inv unfolding bij_betw_def by (by100 blast)
        have h\<sigma>inv_C: "\<sigma>inv ` C = C'" unfolding C'_def \<sigma>inv_def by simp
        have hinj_inv: "inj_on \<sigma>inv UNIV"
          using hbij_inv unfolding bij_betw_def by (by100 blast)
        \<comment> \<open>\<sigma>^{-1}(R^2\C) = \<sigma>^{-1}(UNIV) \ \<sigma>^{-1}(C) = (S^2\{N}) \ C'.\<close>
        have "\<sigma>inv ` (UNIV - C) = (top1_S2 - {north_pole}) - C'"
        proof -
          have "\<sigma>inv ` (UNIV - C) = \<sigma>inv ` UNIV - \<sigma>inv ` C"
            by (rule inj_on_image_set_diff[OF hinj_inv]) blast+
          also have "... = (top1_S2 - {north_pole}) - C'"
            using h\<sigma>inv_img h\<sigma>inv_C by simp
          finally show ?thesis .
        qed
        \<comment> \<open>S^2\C' = ((S^2\{N})\C') \<union> ({N}\C'). N \<notin> C' since C' \<subseteq> S^2\{N}.\<close>
        have "north_pole \<notin> C'" using hC'_sub by (by100 blast)
        hence "top1_S2 - C' = ((top1_S2 - {north_pole}) - C') \<union> {north_pole}"
          using hN_S2 by (by100 blast)
        thus ?thesis using \<open>\<sigma>inv ` (UNIV - C) = (top1_S2 - {north_pole}) - C'\<close> by simp
      qed
      \<comment> \<open>N \<in> closure(\<sigma>^{-1}(R^2\C)) in S^2 topology.\<close>
      have hN_closure: "north_pole \<in> closure_on top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
      proof -
        \<comment> \<open>\<sigma>inv(R^2\C) = (S^2\C')\{N}. Since C' \<subseteq> S^2\{N}, N \<notin> C', N \<in> S^2\C'.
           S^2\C' is open (C' closed = compact in Hausdorff S^2).
           For N \<in> closure((S^2\C')\{N}): every open W \<ni> N intersects (S^2\C')\{N}.
           W \<inter> (S^2\C') is open, contains N. If = {N}, then {N} open in S^2 \<Rightarrow> FALSE.
           So \<exists> point \<noteq> N in W \<inter> (S^2\C') = W \<inter> (S^2\C')\{N}.\<close>
        have hN_notin_C': "north_pole \<notin> C'" using hC'_sub by (by100 blast)
        have hC'_closed: "closedin_on top1_S2 top1_S2_topology C'"
        proof -
          \<comment> \<open>C' = \<sigma>inv(C). \<sigma>inv continuous, C compact \<Rightarrow> C' compact \<Rightarrow> closed in Hausdorff S^2.\<close>
          \<comment> \<open>Actually C' \<subseteq> S^2\{N} \<subseteq> S^2. C' compact in S^2\{N} subspace.
             Compact in Hausdorff \<Rightarrow> closed in Hausdorff \<Rightarrow> closed in S^2.\<close>
          \<comment> \<open>C compact (continuous image of S^1 which is compact).
             \<sigma>inv continuous from R^2 to S^2\{N}. C' = \<sigma>inv(C) compact.\<close>
          have "C \<subseteq> UNIV" by simp
          have hC_compact_std: "compact C"
          proof -
            obtain f where "top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f" "f ` top1_S1 = C"
              using assms unfolding top1_simple_closed_curve_on_def by (by100 blast)
            have "compact top1_S1" using S1_compact
              top1_compact_on_subspace_UNIV_iff_compact[of top1_S1]
              product_topology_on_open_sets_real2
              unfolding top1_S1_topology_def by (by100 simp)
            have "compact (f ` top1_S1)"
            proof (rule compact_continuous_image)
              show "continuous_on top1_S1 f"
                unfolding continuous_on_open_invariant
              proof (intro allI impI)
                fix B :: "(real \<times> real) set" assume "open B"
                have "B \<in> ?TR2" using \<open>open B\<close> product_topology_on_open_sets_real2
                  unfolding top1_open_sets_def by (by100 simp)
                hence "{x \<in> top1_S1. f x \<in> B} \<in> top1_S1_topology"
                  using \<open>top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f\<close>
                  unfolding top1_continuous_map_on_def by (by100 blast)
                then obtain W where "W \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
                    and "{x \<in> top1_S1. f x \<in> B} = top1_S1 \<inter> W"
                  unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
                have "open W" using \<open>W \<in> _\<close> product_topology_on_open_sets_real2
                  unfolding top1_open_sets_def by (by100 simp)
                thus "\<exists>A. open A \<and> A \<inter> top1_S1 = f -` B \<inter> top1_S1"
                  using \<open>{x \<in> top1_S1. f x \<in> B} = top1_S1 \<inter> W\<close> by (by100 blast)
              qed
              show "compact top1_S1" by (rule \<open>compact top1_S1\<close>)
            qed
            thus ?thesis using \<open>f ` top1_S1 = C\<close> by simp
          qed
          have hC'_compact_std: "compact C'"
          proof -
            \<comment> \<open>\<sigma>inv continuous on C (standard topology): bridge from custom.\<close>
            have h\<sigma>inv_cont_std: "continuous_on C \<sigma>inv"
            proof -
              have hinv_cust: "top1_continuous_map_on UNIV ?TR2
                  (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
                  \<sigma>inv"
                using h\<sigma> unfolding top1_homeomorphism_on_def \<sigma>inv_def by (by100 blast)
              show ?thesis unfolding continuous_on_open_invariant
              proof (intro allI impI)
                fix V :: "(real\<times>real\<times>real) set" assume "open V"
                have "V \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                  using \<open>open V\<close> unfolding top1_open_sets_def by simp
                \<comment> \<open>V \<inter> (S^2\{N}) open in subspace S^2\{N}.\<close>
                have hV_sub: "V \<inter> (top1_S2 - {north_pole}) \<in>
                    subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
                proof -
                  have hR3eq: "top1_S2_topology = subspace_topology UNIV
                      (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                    unfolding top1_S2_topology_def
                    using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                          product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
                  have hS2N_sub: "top1_S2 - {north_pole} \<subseteq> top1_S2" by (by100 blast)
                  have "subspace_topology top1_S2 (subspace_topology UNIV
                      (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2) (top1_S2 - {north_pole})
                      = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {north_pole})"
                    by (rule subspace_topology_trans[OF hS2N_sub])
                  hence "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})
                      = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {north_pole})"
                    using hR3eq by simp
                  thus ?thesis using \<open>V \<in> top1_open_sets\<close> unfolding subspace_topology_def by (by100 blast)
                qed
                \<comment> \<open>Preimage under \<sigma>inv: {y \<in> UNIV. \<sigma>inv y \<in> V \<inter> (S^2\{N})} \<in> TR2.\<close>
                have "{y \<in> UNIV. \<sigma>inv y \<in> V \<inter> (top1_S2 - {north_pole})}
                    \<in> product_topology_on top1_open_sets top1_open_sets"
                  using hinv_cust hV_sub unfolding top1_continuous_map_on_def by (by100 blast)
                \<comment> \<open>Since \<sigma>inv always maps into S^2\{N}, preimage of V = preimage of V \<inter> (S^2\{N}).\<close>
                have "\<forall>y. \<sigma>inv y \<in> top1_S2 - {north_pole}"
                  using hinv_cust unfolding top1_continuous_map_on_def by (by100 blast)
                hence heq: "{y \<in> UNIV. \<sigma>inv y \<in> V} = {y \<in> UNIV. \<sigma>inv y \<in> V \<inter> (top1_S2 - {north_pole})}"
                  by (by100 blast)
                have "{y \<in> UNIV. \<sigma>inv y \<in> V} \<in> product_topology_on top1_open_sets top1_open_sets"
                  using \<open>{y \<in> UNIV. \<sigma>inv y \<in> V \<inter> _} \<in> _\<close> heq by simp
                hence "open {y. \<sigma>inv y \<in> V}"
                  using product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 simp)
                moreover have "{y. \<sigma>inv y \<in> V} \<inter> C = \<sigma>inv -` V \<inter> C" by (by100 blast)
                ultimately show "\<exists>T. open T \<and> T \<inter> C = \<sigma>inv -` V \<inter> C" by (by100 blast)
              qed
            qed
            show ?thesis unfolding C'_def
              by (rule compact_continuous_image[OF h\<sigma>inv_cont_std hC_compact_std])
          qed
          have "closed C'" using compact_imp_closed[OF hC'_compact_std] .
          \<comment> \<open>closed in R^3 + C' \<subseteq> S^2 \<Rightarrow> closed in S^2 (subspace).\<close>
          show ?thesis unfolding closedin_on_def
          proof (intro conjI)
            show "C' \<subseteq> top1_S2" by (rule hC'_sub_S2)
            show "top1_S2 - C' \<in> top1_S2_topology"
            proof -
              have "open (- C')" using open_Compl[OF \<open>closed C'\<close>] .
              have hR3eq: "top1_S2_topology = subspace_topology UNIV
                  (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                unfolding top1_S2_topology_def
                using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                      product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
              have "- C' \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                using \<open>open (- C')\<close> unfolding top1_open_sets_def by simp
              have "top1_S2 \<inter> (- C') = top1_S2 - C'" by (by100 blast)
              have "top1_S2 - C' \<in> subspace_topology UNIV
                  (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                using \<open>- C' \<in> top1_open_sets\<close> \<open>top1_S2 \<inter> (- C') = top1_S2 - C'\<close>
                unfolding subspace_topology_def by (by100 blast)
              thus ?thesis using hR3eq by simp
            qed
          qed
        qed
        have hS2C'_open: "top1_S2 - C' \<in> top1_S2_topology"
        proof -
          have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
            using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          show ?thesis using hC'_closed hTS2_loc unfolding closedin_on_def is_topology_on_def
            by (by100 blast)
        qed
        have hN_in_S2C': "north_pole \<in> top1_S2 - C'" using hN_S2 hN_notin_C' by (by100 blast)
        \<comment> \<open>\<sigma>inv(R^2\C) = (S^2\{N})\C' = (S^2\C')\{N}.\<close>
        have h\<sigma>inv_eq: "\<sigma>inv ` (UNIV - C) = (top1_S2 - C') - {north_pole}"
        proof -
          have "top1_S2 - C' = \<sigma>inv ` (UNIV - C) \<union> {north_pole}" by (rule hS2C'_eq)
          moreover have "north_pole \<notin> \<sigma>inv ` (UNIV - C)"
          proof -
            have hbij_\<sigma>: "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
              using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
            have "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
              unfolding \<sigma>inv_def by (rule bij_betw_inv_into[OF hbij_\<sigma>])
            hence "\<sigma>inv ` UNIV \<subseteq> top1_S2 - {north_pole}"
              unfolding bij_betw_def by (by100 blast)
            hence "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - {north_pole}" by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        \<comment> \<open>N \<in> closure((S^2\C')\{N}): same as S2_connected argument.\<close>
        show ?thesis unfolding h\<sigma>inv_eq closure_on_def
        proof (rule InterI)
          fix D assume hD: "D \<in> {Ca. closedin_on top1_S2 top1_S2_topology Ca \<and>
              (top1_S2 - C') - {north_pole} \<subseteq> Ca}"
          hence hD_closed: "closedin_on top1_S2 top1_S2_topology D"
              and hD_sup: "(top1_S2 - C') - {north_pole} \<subseteq> D" by auto
          have "top1_S2 - D \<subseteq> C' \<union> {north_pole}"
          proof -
            have "top1_S2 - D \<subseteq> top1_S2 - ((top1_S2 - C') - {north_pole})"
              using hD_sup by (by100 blast)
            also have "... \<subseteq> C' \<union> {north_pole}" by (by100 blast)
            finally show ?thesis .
          qed
          have hD_open: "top1_S2 - D \<in> top1_S2_topology"
          proof -
            have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
              using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
            show ?thesis using hD_closed hTS2_loc unfolding closedin_on_def is_topology_on_def
              by (by100 blast)
          qed
          \<comment> \<open>If N \<notin> D: then N \<in> S^2\D which is open and \<subseteq> C'\<union>{N}.
             So S^2\D is open and contained in C'\<union>{N}. Since N \<in> S^2\D,
             S^2\D \<inter> (S^2\C') is open (intersection of opens) and contains... hmm.
             Actually: S^2\D \<subseteq> C'\<union>{N} and N \<in> S^2\D.
             (S^2\D)\{N} \<subseteq> C'. And S^2\D is open. If S^2\D = {N}, then {N} open → FALSE.
             If S^2\D has another point x \<noteq> N, then x \<in> C'. But also x \<in> S^2\D \<subseteq> S^2.
             Actually S^2\D is open and \<subseteq> C'\<union>{N}. The complement S^2\(C'\<union>{N}) \<subseteq> D.
             Since C'\<union>{N} is closed (C' closed, {N} closed in Hausdorff, finite union of closed),
             S^2\(C'\<union>{N}) is open. So D \<supseteq> open set.
             Hmm, this doesn't directly help.\<close>
          show "north_pole \<in> D"
          proof (rule ccontr)
            assume "north_pole \<notin> D"
            hence "north_pole \<in> top1_S2 - D" using hN_S2 by (by100 blast)
            \<comment> \<open>S^2\D is open, \<subseteq> C'\<union>{N}, contains N.
               If S^2\D = {N}: {N} open in S^2 \<Rightarrow> FALSE (proved in S2_connected).\<close>
            have "top1_S2 - D \<subseteq> C' \<union> {north_pole}" by (rule \<open>top1_S2 - D \<subseteq> C' \<union> {north_pole}\<close>)
            \<comment> \<open>(S^2\D) \<inter> (S^2\C') \<subseteq> {N}.\<close>
            have "(top1_S2 - D) \<inter> (top1_S2 - C') \<subseteq> {north_pole}"
              using \<open>top1_S2 - D \<subseteq> C' \<union> {north_pole}\<close> by (by100 blast)
            \<comment> \<open>(S^2\D) \<inter> (S^2\C') open (intersection of opens) and contains N.\<close>
            have "(top1_S2 - D) \<inter> (top1_S2 - C') \<in> top1_S2_topology"
            proof -
              have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
                using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
              show ?thesis by (rule topology_inter_open[OF hTS2_loc hD_open hS2C'_open])
            qed
            have "north_pole \<in> (top1_S2 - D) \<inter> (top1_S2 - C')"
              using \<open>north_pole \<in> top1_S2 - D\<close> hN_in_S2C' by (by100 blast)
            \<comment> \<open>So (S^2\D) \<inter> (S^2\C') is a nonempty open set \<subseteq> {N}. Hence = {N}. So {N} \<in> S^2_topology.\<close>
            hence "(top1_S2 - D) \<inter> (top1_S2 - C') = {north_pole}"
              using \<open>(top1_S2 - D) \<inter> (top1_S2 - C') \<subseteq> {north_pole}\<close> by (by100 blast)
            hence "{north_pole} \<in> top1_S2_topology"
              using \<open>(top1_S2 - D) \<inter> (top1_S2 - C') \<in> top1_S2_topology\<close> by simp
            \<comment> \<open>{N} open in S^2 \<Rightarrow> FALSE (same argument as S2_connected).\<close>
            show False using singleton_not_open_in_S2[OF hN_S2] \<open>{north_pole} \<in> top1_S2_topology\<close> by simp
          qed
        qed
      qed
      \<comment> \<open>Connected set \<union> limit point = connected. Use Theorem 23.4.\<close>
      have "top1_connected_on (top1_S2 - C') (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C'))"
      proof -
        have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
          using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hA_sub_S2: "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2"
        proof -
          have "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - {north_pole}"
          proof -
            have h\<sigma>inv_img_sub: "\<sigma>inv ` UNIV \<subseteq> top1_S2 - {north_pole}"
            proof -
              have hbij: "bij_betw \<sigma> (top1_S2 - {north_pole}) UNIV"
                using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
              have "bij_betw \<sigma>inv UNIV (top1_S2 - {north_pole})"
                unfolding \<sigma>inv_def by (rule bij_betw_inv_into[OF hbij])
              thus ?thesis unfolding bij_betw_def by (by100 blast)
            qed
            thus ?thesis by (by100 blast)
          qed
          thus ?thesis by (by100 blast)
        qed
        have hB_sub_S2: "top1_S2 - C' \<subseteq> top1_S2" by (by100 blast)
        have hA_sub_B: "\<sigma>inv ` (UNIV - C) \<subseteq> top1_S2 - C'"
          using hS2C'_eq by (by100 blast)
        have hB_sub_cl: "top1_S2 - C' \<subseteq> closure_on top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
        proof -
          have hA_sub_cl: "\<sigma>inv ` (UNIV - C) \<subseteq> closure_on top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
            by (rule subset_closure_on)
          have hN_in_cl: "north_pole \<in> closure_on top1_S2 top1_S2_topology (\<sigma>inv ` (UNIV - C))"
            by (rule hN_closure)
          show ?thesis using hS2C'_eq hA_sub_cl hN_in_cl by (by100 blast)
        qed
        show ?thesis
          by (rule Theorem_23_4[OF hTS2_loc hA_sub_S2 hB_sub_S2 hA_sub_B hB_sub_cl h\<sigma>inv_R2C_conn])
      qed
      thus False using hS2_C'_sep unfolding top1_separates_on_def by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 2 (Exactly two components): Decompose C = C_1 \<union> C_2 (two arcs with endpoints a, b).
     Transfer to S^2, apply Theorem 63.5 (via 63.2 + 63.3), transfer back.\<close>
  \<comment> \<open>Step 2a: Decompose C into two arcs.\<close>
  \<comment> \<open>Step 2b: Transfer arcs to S^2 via \<sigma>^{-1}. Get SCC and two arcs on S^2.\<close>
  \<comment> \<open>Step 2c: By 63.2, arcs don't separate S^2. By 63.5, exactly 2 components on S^2.\<close>
  \<comment> \<open>Step 2d: Transfer 2 components back to R^2.\<close>
  obtain U V where hUV_ne: "U \<noteq> {}" "V \<noteq> {}" and hUV_disj: "U \<inter> V = {}"
      and hUV_cover: "U \<union> V = UNIV - C"
      and hU_conn: "top1_connected_on U (subspace_topology UNIV ?TR2 U)"
      and hV_conn: "top1_connected_on V (subspace_topology UNIV ?TR2 V)"
      and hU_bdd_raw: "\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M"
      and hV_unbdd_raw: "\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M"
      and hU_bdy_raw: "closure U = U \<union> C"
      and hV_bdy_raw: "closure V = V \<union> C"
  proof -
    \<comment> \<open>Step 2a: Decompose C into two arcs C1, C2 with C1 \<inter> C2 = {p, q}.\<close>
    obtain C1_arc C2_arc p_arc q_arc where
        hC_decomp: "C = C1_arc \<union> C2_arc"
        and hC_inter: "C1_arc \<inter> C2_arc = {p_arc, q_arc}"
        and hpq_ne: "p_arc \<noteq> q_arc"
        and hC1_arc: "top1_is_arc_on C1_arc
            (subspace_topology UNIV ?TR2 C1_arc)"
        and hC2_arc: "top1_is_arc_on C2_arc
            (subspace_topology UNIV ?TR2 C2_arc)"
    proof -
      have hR2_strict: "is_topology_on_strict (UNIV :: (real\<times>real) set) ?TR2"
      proof -
        have "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding is_topology_on_strict_def by (by100 blast)
      qed
      have hR2_haus: "is_hausdorff_on (UNIV :: (real\<times>real) set) ?TR2"
        by (rule top1_R2_is_hausdorff)
      obtain A1 A2 aa bb where hd: "C = A1 \<union> A2" "A1 \<inter> A2 = {aa, bb}" "aa \<noteq> bb"
          "top1_is_arc_on A1 (subspace_topology UNIV ?TR2 A1)"
          "top1_is_arc_on A2 (subspace_topology UNIV ?TR2 A2)"
        using simple_closed_curve_arc_decomposition[OF assms hR2_strict hR2_haus] by (by100 blast)
      show ?thesis using hd by (intro that[of A1 A2 aa bb]) (by100 blast)+
    qed
    \<comment> \<open>Step 2b: Transfer to S^2 via \<sigma>^{-1}. Get arcs C1', C2' on S^2.\<close>
    \<comment> \<open>Step 2c: On S^2: C1', C2' are arcs (don't separate by 63.2).
       C1' \<inter> C2' = {p', q'}, card = 2. C1', C2' closed, connected.
       By 63.5: C1' \<union> C2' separates S^2 into exactly 2 components.\<close>
    \<comment> \<open>Step 2d: Transfer 2 components back to R^2.\<close>
    \<comment> \<open>Step 2e: Identify bounded/unbounded. Boundary = C.\<close>
    \<comment> \<open>Step 2b: Transfer arcs to S^2 via \<sigma>^{-1} (same as step 1 transfer).
       Step 2c: On S^2, apply 63.2 (arcs don't separate — PROVED!) and
       63.5 (exactly 2 components — needs 63.1(c)+\<pi>_1\<cong>Z).
       Step 2d: Transfer back to R^2.
       Step 2e: Bounded/unbounded + boundary.\<close>
    \<comment> \<open>C1_arc, C2_arc don't separate S^2 (by Theorem_63_2 applied on S^2).
       This requires transferring arcs to S^2 and applying 63.2 there.
       The transfer uses the same \<sigma>^{-1} as in step 1.\<close>
    \<comment> \<open>C1_arc and C2_arc don't separate S^2 (by Theorem_63_2 after transfer).
       The transfer requires re-obtaining \<sigma>^{-1} (it was local to hC_sep proof).\<close>
    \<comment> \<open>NOTE: \<sigma>inv is not in scope here (it was inside hC_sep's proof block).
       The proof requires: obtain \<sigma>, define \<sigma>inv, transfer arcs, apply 63.2.\<close>
    \<comment> \<open>By 63.5: exactly 2 components on S^2.\<close>
    \<comment> \<open>Transfer back to R^2 and identify bounded/unbounded.\<close>
    show ?thesis sorry \<comment> \<open>Needs:
       - 63.5 (SORRY) with C1'=\<sigma>^{-1}(C1_arc), C2'=\<sigma>^{-1}(C2_arc)
       - Transfer 2 S^2-components to R^2-components via \<sigma>
       - One bounded (interior), one unbounded (exterior)
       - Boundary = C (Munkres Step 2 argument)\<close>
  qed
  \<comment> \<open>Step 3 (Path-connected): R^2 is locally path-connected, so components are path-connected.\<close>
  \<comment> \<open>First show UNIV-C is open (C compact hence closed).\<close>
  have hUNIV_C_open_global: "UNIV - C \<in> ?TR2"
  proof -
    obtain f where "top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f" "f ` top1_S1 = C"
      using assms unfolding top1_simple_closed_curve_on_def by (by100 blast)
    have "compact top1_S1" using S1_compact
      top1_compact_on_subspace_UNIV_iff_compact[of top1_S1]
      product_topology_on_open_sets_real2
      unfolding top1_S1_topology_def by (by100 simp)
    have "compact C"
    proof -
      have "compact (f ` top1_S1)"
      proof (rule compact_continuous_image)
        show "continuous_on top1_S1 f"
          unfolding continuous_on_open_invariant
        proof (intro allI impI)
          fix B :: "(real \<times> real) set" assume hBo: "open B"
          have "B \<in> ?TR2" using hBo product_topology_on_open_sets_real2
            unfolding top1_open_sets_def by (by100 simp)
          hence "{x \<in> top1_S1. f x \<in> B} \<in> top1_S1_topology"
            using \<open>top1_continuous_map_on top1_S1 top1_S1_topology UNIV ?TR2 f\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          then obtain W where hW: "W \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
              and heq: "{x \<in> top1_S1. f x \<in> B} = top1_S1 \<inter> W"
            unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
          have "open W" using hW product_topology_on_open_sets_real2
            unfolding top1_open_sets_def by (by100 simp)
          moreover have "W \<inter> top1_S1 = f -` B \<inter> top1_S1"
            using heq by (by100 blast)
          ultimately show "\<exists>A. open A \<and> A \<inter> top1_S1 = f -` B \<inter> top1_S1" by (by100 blast)
        qed
        show "compact top1_S1" by (rule \<open>compact top1_S1\<close>)
      qed
      thus ?thesis using \<open>f ` top1_S1 = C\<close> by simp
    qed
    hence "closed C" by (rule compact_imp_closed)
    hence "open (- C)" by (rule open_Compl)
    hence "open (UNIV - C)" by (simp add: Compl_eq_Diff_UNIV)
    thus ?thesis using product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 simp)
  qed
  have hUNIV_C_lpc_global: "top1_locally_path_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
    by (rule open_subset_locally_path_connected[OF R2_locally_path_connected hUNIV_C_open_global]) simp
  have hU_pc: "top1_path_connected_on U (subspace_topology UNIV ?TR2 U)"
  proof -
    have hTU: "is_topology_on U (subspace_topology UNIV ?TR2 U)"
      using hU_conn unfolding top1_connected_on_def by (by100 blast)
    have hU_locp: "top1_locally_path_connected_on U (subspace_topology UNIV ?TR2 U)"
    proof -
      \<comment> \<open>UNIV-C is open in R^2. U \<subseteq> UNIV-C. U is open in UNIV-C (component of lpc space).
         Open subset of R^2 is lpc. U open subset of that.\<close>
      have hUNIV_C_open: "UNIV - C \<in> ?TR2" by (rule hUNIV_C_open_global)
      have hUNIV_C_lpc: "top1_locally_path_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        by (rule hUNIV_C_lpc_global)
      \<comment> \<open>U is open in UNIV-C (component of lpc open space).\<close>
      have hU_open_in_UC: "U \<in> subspace_topology UNIV ?TR2 (UNIV - C)"
      proof -
        \<comment> \<open>U is a connected component of UNIV-C (lpc space). Components of lpc = open.\<close>
        have hTUC: "is_topology_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        proof -
          have "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
            using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
          thus ?thesis by (rule subspace_topology_is_topology_on) simp
        qed
        obtain u where hu: "u \<in> U" using hUV_ne(1) by (by100 blast)
        have hu_UC: "u \<in> UNIV - C" using hu hUV_cover by (by100 blast)
        \<comment> \<open>The path component of u in UNIV-C equals U.
           By Theorem 25.5, in lpc space path component = component.\<close>
        have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u = U"
        proof -
          \<comment> \<open>U is a connected component: U connected, U \<subseteq> UNIV-C, U maximal.
             In lpc space, path component = component (Theorem 25.5).\<close>
          have "top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u = U"
          proof -
            \<comment> \<open>U is a component of UNIV-C: it's connected, and any connected set containing u
               that is bigger than U would have to intersect V, but U \<inter> V = {} and both open.\<close>
            \<comment> \<open>component_of(u) = \<Union>{C \<subseteq> UNIV-C. u \<in> C \<and> connected C}.\<close>
            \<comment> \<open>U \<subseteq> component_of(u): U is connected and u \<in> U.\<close>
            have hU_sub_comp: "U \<subseteq> top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u"
              unfolding top1_component_of_on_def
            proof
              fix x assume hxU: "x \<in> U"
              have hUsub: "U \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
              moreover have "u \<in> U" using hu by simp
              moreover have "top1_connected_on U (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U)"
              proof -
                have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U
                    = subspace_topology UNIV ?TR2 U"
                  by (rule subspace_topology_trans[OF hUsub])
                thus ?thesis using hU_conn by simp
              qed
              ultimately show "x \<in> \<Union>{Ca. Ca \<subseteq> UNIV - C \<and> u \<in> Ca \<and>
                  top1_connected_on Ca (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) Ca)}"
                using hxU hUsub by (by100 blast)
            qed
            \<comment> \<open>component_of(u) \<subseteq> U: any connected C with u \<in> C \<subseteq> UNIV-C lies in U.
               (If C intersected V, C = (C\<inter>U) \<union> (C\<inter>V) with both open in C, contradicting connected.)\<close>
            have hcomp_sub_U: "top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u \<subseteq> U"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then obtain v where hv_comp: "v \<in> top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u"
                  and hv_notU: "v \<notin> U" by (by100 blast)
              have hv_UC: "v \<in> UNIV - C"
                using hv_comp unfolding top1_component_of_on_def by (by100 blast)
              hence "v \<in> V" using hv_notU hUV_cover by (by100 blast)
              \<comment> \<open>component_of(u) is connected. V is connected. They share v.\<close>
              have hcomp_conn: "top1_connected_on (top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u)
                  (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))
                    (top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u))"
                by (rule top1_component_of_on_connected[OF hTUC hu_UC])
              \<comment> \<open>comp(u) \<union> V is connected (share point v) and = UNIV-C.\<close>
              have hcomp_V_conn: "top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
              proof -
                let ?comp = "top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u"
                define A :: "nat \<Rightarrow> (real \<times> real) set" where "A = (\<lambda>i. if i = 0 then ?comp else V)"
                have hI: "{0::nat, 1} \<noteq> {}" by simp
                have hV_sub: "V \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
                have hcomp_sub: "?comp \<subseteq> UNIV - C" unfolding top1_component_of_on_def by (by100 blast)
                have hAsub: "\<forall>i\<in>{0::nat,1}. A i \<subseteq> UNIV - C"
                  unfolding A_def using hV_sub hcomp_sub by auto
                have hAconn: "\<forall>i\<in>{0::nat,1}. top1_connected_on (A i) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (A i))"
                proof
                  fix i :: nat assume "i \<in> {0, 1}"
                  show "top1_connected_on (A i) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (A i))"
                  proof (cases "i = 0")
                    case True thus ?thesis unfolding A_def using hcomp_conn by simp
                  next
                    case False
                    have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V
                        = subspace_topology UNIV ?TR2 V"
                      by (rule subspace_topology_trans[OF hV_sub])
                    thus ?thesis using False unfolding A_def using hV_conn by simp
                  qed
                qed
                have hv_inter: "v \<in> \<Inter>(A ` {0::nat, 1})"
                  unfolding A_def using hv_comp \<open>v \<in> V\<close> by simp
                have hY_eq: "(\<Union>i\<in>{0::nat,1}. A i) = UNIV - C"
                proof -
                  have "?comp \<union> V \<supseteq> U \<union> V" using hU_sub_comp by (by100 blast)
                  hence "?comp \<union> V = UNIV - C" using hUV_cover
                    unfolding top1_component_of_on_def by (by100 blast)
                  moreover have "(\<Union>i\<in>{0::nat,1}. A i) = ?comp \<union> V" unfolding A_def by auto
                  ultimately show ?thesis by simp
                qed
                have "top1_connected_on (\<Union>i\<in>{0::nat,1}. A i) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (\<Union>i\<in>{0::nat,1}. A i))"
                  by (rule Theorem_23_3[OF hTUC hI hAsub hAconn hv_inter])
                hence "top1_connected_on (UNIV - C) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (UNIV - C))"
                  using hY_eq by simp
                moreover have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (UNIV - C)
                    = subspace_topology UNIV ?TR2 (UNIV - C)"
                  by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
                ultimately show ?thesis by simp
              qed
              show False using hC_sep hcomp_V_conn by simp
            qed
            show ?thesis using hU_sub_comp hcomp_sub_U by (by100 blast)
          qed
          moreover have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u
              = top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u"
            using Theorem_25_5[OF hTUC] hUNIV_C_lpc_global hu_UC by (by100 blast)
          ultimately show ?thesis by simp
        qed
        moreover have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) u
            \<in> subspace_topology UNIV ?TR2 (UNIV - C)"
          by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTUC hUNIV_C_lpc hu_UC])
        ultimately show ?thesis by simp
      qed
      have hU_sub_UC: "U \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
      have "top1_locally_path_connected_on U
          (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U)"
        by (rule open_subset_locally_path_connected[OF hUNIV_C_lpc hU_open_in_UC hU_sub_UC])
      moreover have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U
          = subspace_topology UNIV ?TR2 U"
        by (rule subspace_topology_trans[OF hU_sub_UC])
      ultimately show ?thesis by simp
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTU hU_conn hU_locp hUV_ne(1)])
  qed
  have hV_pc: "top1_path_connected_on V (subspace_topology UNIV ?TR2 V)"
  proof -
    have hTV: "is_topology_on V (subspace_topology UNIV ?TR2 V)"
      using hV_conn unfolding top1_connected_on_def by (by100 blast)
    have hV_locp: "top1_locally_path_connected_on V (subspace_topology UNIV ?TR2 V)"
    proof -
      have hUNIV_C_open: "UNIV - C \<in> ?TR2" by (rule hUNIV_C_open_global)
      have hUNIV_C_lpc: "top1_locally_path_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        by (rule hUNIV_C_lpc_global)
      have hV_open_in_UC: "V \<in> subspace_topology UNIV ?TR2 (UNIV - C)"
      proof -
        have hTUC: "is_topology_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))"
        proof -
          have "is_topology_on (UNIV::(real\<times>real) set) ?TR2"
            using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
          thus ?thesis by (rule subspace_topology_is_topology_on) simp
        qed
        obtain v where hv: "v \<in> V" using hUV_ne(2) by (by100 blast)
        have hv_UC: "v \<in> UNIV - C" using hv hUV_cover by (by100 blast)
        have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) v = V"
        proof -
          let ?comp_v = "top1_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) v"
          have hV_sub': "V \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
          have hV_sub_comp: "V \<subseteq> ?comp_v"
            unfolding top1_component_of_on_def
          proof
            fix x assume hxV: "x \<in> V"
            have "top1_connected_on V (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V)"
            proof -
              have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V
                  = subspace_topology UNIV ?TR2 V" by (rule subspace_topology_trans[OF hV_sub'])
              thus ?thesis using hV_conn by simp
            qed
            thus "x \<in> \<Union>{Ca. Ca \<subseteq> UNIV - C \<and> v \<in> Ca \<and>
                top1_connected_on Ca (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) Ca)}"
              using hxV hV_sub' hv by (by100 blast)
          qed
          have hcomp_v_sub_V: "?comp_v \<subseteq> V"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then obtain w where hw_comp: "w \<in> ?comp_v" and hw_notV: "w \<notin> V" by (by100 blast)
            have hw_UC: "w \<in> UNIV - C" using hw_comp unfolding top1_component_of_on_def by (by100 blast)
            hence "w \<in> U" using hw_notV hUV_cover by (by100 blast)
            have hcomp_v_conn: "top1_connected_on ?comp_v
                (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) ?comp_v)"
              by (rule top1_component_of_on_connected[OF hTUC hv_UC])
            have hU_sub': "U \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
            have hU_conn_sub: "top1_connected_on U
                (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U)"
            proof -
              have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) U
                  = subspace_topology UNIV ?TR2 U" by (rule subspace_topology_trans[OF hU_sub'])
              thus ?thesis using hU_conn by simp
            qed
            define B :: "nat \<Rightarrow> (real \<times> real) set" where "B = (\<lambda>i. if i = 0 then ?comp_v else U)"
            have "w \<in> \<Inter>(B ` {0::nat, 1})" unfolding B_def using hw_comp \<open>w \<in> U\<close> by simp
            moreover have "\<forall>i\<in>{0::nat,1}. B i \<subseteq> UNIV - C"
              unfolding B_def using hU_sub' unfolding top1_component_of_on_def by auto
            moreover have "\<forall>i\<in>{0::nat,1}. top1_connected_on (B i)
                (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (B i))"
            proof
              fix i :: nat assume "i \<in> {0, 1}"
              show "top1_connected_on (B i) (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (B i))"
                unfolding B_def using hcomp_v_conn hU_conn_sub by auto
            qed
            ultimately have "top1_connected_on (\<Union>i\<in>{0::nat,1}. B i)
                (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (\<Union>i\<in>{0::nat,1}. B i))"
              using Theorem_23_3[OF hTUC, of "{0::nat,1}" B w] by (by100 blast)
            moreover have "(\<Union>i\<in>{0::nat,1}. B i) = UNIV - C"
            proof -
              have "?comp_v \<union> U \<supseteq> V \<union> U" using hV_sub_comp by (by100 blast)
              thus ?thesis unfolding B_def using hUV_cover
                unfolding top1_component_of_on_def by auto
            qed
            moreover have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) (UNIV - C)
                = subspace_topology UNIV ?TR2 (UNIV - C)"
              by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
            ultimately have "top1_connected_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C))" by simp
            thus False using hC_sep by simp
          qed
          have "?comp_v = V" using hV_sub_comp hcomp_v_sub_V by (by100 blast)
          moreover have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) v = ?comp_v"
            using Theorem_25_5[OF hTUC] hUNIV_C_lpc_global hv_UC by (by100 blast)
          ultimately show ?thesis by simp
        qed
        moreover have "top1_path_component_of_on (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) v
            \<in> subspace_topology UNIV ?TR2 (UNIV - C)"
          by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTUC hUNIV_C_lpc_global hv_UC])
        ultimately show ?thesis by simp
      qed
      have hV_sub_UC: "V \<subseteq> UNIV - C" using hUV_cover by (by100 blast)
      have "top1_locally_path_connected_on V
          (subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V)"
        by (rule open_subset_locally_path_connected[OF hUNIV_C_lpc hV_open_in_UC hV_sub_UC])
      moreover have "subspace_topology (UNIV - C) (subspace_topology UNIV ?TR2 (UNIV - C)) V
          = subspace_topology UNIV ?TR2 V"
        by (rule subspace_topology_trans[OF hV_sub_UC])
      ultimately show ?thesis by simp
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTV hV_conn hV_locp hUV_ne(2)])
  qed
  \<comment> \<open>Step 4 (Bounded/unbounded): Under stereographic projection, one component maps to
     the bounded component and the other to the unbounded one (Lemma 61.1).\<close>
  have hU_bdd: "\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M" by (rule hU_bdd_raw)
  have hV_unbdd: "\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M" by (rule hV_unbdd_raw)
  \<comment> \<open>Step 5 (Boundary = C): Both components have C as their common boundary.\<close>
  have hU_bdy: "closure U = U \<union> C" by (rule hU_bdy_raw)
  have hV_bdy: "closure V = V \<union> C" by (rule hV_bdy_raw)
  show ?thesis using hUV_ne hUV_disj hUV_cover hU_pc hV_pc hU_bdd hV_unbdd hU_bdy hV_bdy
    by blast
qed

\<comment> \<open>Helper for 63.5: 3+ open components of S^2-(C1\<union>C2) give a contradiction.
   This encapsulates the 63.1(a)+(c) + \<pi>_1\<cong>Z argument.\<close>
lemma three_components_contradiction:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology C1"
  and "closedin_on top1_S2 top1_S2_topology C2"
  and "top1_connected_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
  and "top1_connected_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
  and "card (C1 \<inter> C2) = 2"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C2"
  \<comment> \<open>Three disjoint nonempty open (in S^2) subsets covering S^2-(C1\<union>C2).\<close>
  and "W1 \<in> top1_S2_topology" and "W2 \<in> top1_S2_topology" and "B \<in> top1_S2_topology"
  and "W1 \<noteq> {}" and "W2 \<noteq> {}" and "B \<noteq> {}"
  and "W1 \<inter> W2 = {}" and "W1 \<inter> B = {}" and "W2 \<inter> B = {}"
  and "W1 \<union> W2 \<union> B = top1_S2 - (C1 \<union> C2)"
  shows False
proof -
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hC1sub: "C1 \<subseteq> top1_S2" using assms(2) unfolding closedin_on_def by (by100 blast)
  have hC2sub: "C2 \<subseteq> top1_S2" using assms(3) unfolding closedin_on_def by (by100 blast)
  obtain p q where hpq: "C1 \<inter> C2 = {p, q}" and hpq_ne: "p \<noteq> q"
    using assms(6) card_2_iff by (by100 metis)
  have hp_S2: "p \<in> top1_S2" and hq_S2: "q \<in> top1_S2"
    using hpq hC1sub by (by100 blast)+
  define X where "X = top1_S2 - {p} - {q}"
  define TX where "TX = subspace_topology top1_S2 top1_S2_topology X"
  define U where "U = top1_S2 - C1"
  define V where "V = top1_S2 - C2"
  have hX_eq: "U \<union> V = X"
    unfolding U_def V_def X_def using hpq by (by100 blast)
  have hUV_eq: "U \<inter> V = top1_S2 - (C1 \<union> C2)"
    unfolding U_def V_def by (by100 blast)
  have hTX: "is_topology_on X TX"
    unfolding TX_def by (rule subspace_topology_is_topology_on[OF hTS2])
      (unfold X_def, by100 blast)
  \<comment> \<open>Subsets and openness.\<close>
  have hU_sub_X: "U \<subseteq> X" unfolding U_def X_def using hpq hC1sub by (by100 blast)
  have hV_sub_X: "V \<subseteq> X" unfolding V_def X_def using hpq hC2sub by (by100 blast)
  have hU_open: "openin_on X TX U"
  proof -
    have "U \<in> top1_S2_topology"
      using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def U_def by (by100 blast)
    thus ?thesis unfolding openin_on_def TX_def subspace_topology_def using hU_sub_X by (by100 blast)
  qed
  have hV_open: "openin_on X TX V"
  proof -
    have "V \<in> top1_S2_topology"
      using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def V_def by (by100 blast)
    thus ?thesis unfolding openin_on_def TX_def subspace_topology_def using hV_sub_X by (by100 blast)
  qed
  \<comment> \<open>Path-connectivity.\<close>
  have hU_pc: "top1_path_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
  proof -
    have hU_conn: "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      using assms(7) unfolding top1_separates_on_def U_def by (by100 blast)
    have hU_S2: "U \<in> top1_S2_topology"
      using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def U_def by (by100 blast)
    have hU_lpc: "top1_locally_path_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hU_S2])
         (unfold U_def, by100 blast)
    have hTU: "is_topology_on U (subspace_topology top1_S2 top1_S2_topology U)"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (unfold U_def, by100 blast)
    have "U \<noteq> {}"
    proof -
      have "C2 \<noteq> {p, q}"
      proof
        assume "C2 = {p, q}"
        have "{p} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {q} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hq_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{p} = {p, q} \<inter> (top1_S2 - {q})" using hpq_ne hp_S2 by (by100 auto)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "{q} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {p} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hp_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{q} = {p, q} \<inter> (top1_S2 - {p})" using hpq_ne hq_S2 by (by100 auto)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<not> top1_connected_on {p, q} (subspace_topology top1_S2 top1_S2_topology {p, q})"
          unfolding top1_connected_on_def
          using \<open>{p} \<in> _\<close> \<open>{q} \<in> _\<close> hpq_ne by (by100 blast)
        thus False using assms(5) \<open>C2 = {p, q}\<close> by (by100 simp)
      qed
      moreover have "{p, q} \<subseteq> C2" using hpq by (by100 blast)
      ultimately obtain c where "c \<in> C2" "c \<notin> {p, q}" by (by100 blast)
      hence "c \<notin> C1" using hpq by (by100 blast)
      hence "c \<in> U" unfolding U_def using \<open>c \<in> C2\<close> hC2sub by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTU hU_conn hU_lpc \<open>U \<noteq> {}\<close>])
  qed
  have hV_pc: "top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
  proof -
    have hV_conn: "top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      using assms(8) unfolding top1_separates_on_def V_def by (by100 blast)
    have hV_S2: "V \<in> top1_S2_topology"
      using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def V_def by (by100 blast)
    have hV_lpc: "top1_locally_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hV_S2])
         (unfold V_def, by100 blast)
    have hTV: "is_topology_on V (subspace_topology top1_S2 top1_S2_topology V)"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (unfold V_def, by100 blast)
    have "V \<noteq> {}"
    proof -
      have "C1 \<noteq> {p, q}"
      proof
        assume "C1 = {p, q}"
        have "{p} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {q} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hq_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{p} = {p, q} \<inter> (top1_S2 - {q})" using hpq_ne hp_S2 by (by100 auto)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "{q} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {p} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hp_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{q} = {p, q} \<inter> (top1_S2 - {p})" using hpq_ne hq_S2 by (by100 auto)
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<not> top1_connected_on {p, q} (subspace_topology top1_S2 top1_S2_topology {p, q})"
          unfolding top1_connected_on_def
          using \<open>{p} \<in> _\<close> \<open>{q} \<in> _\<close> hpq_ne by (by100 blast)
        thus False using assms(4) \<open>C1 = {p, q}\<close> by (by100 simp)
      qed
      moreover have "{p, q} \<subseteq> C1" using hpq by (by100 blast)
      ultimately obtain c where "c \<in> C1" "c \<notin> {p, q}" by (by100 blast)
      hence "c \<notin> C2" using hpq by (by100 blast)
      hence "c \<in> V" unfolding V_def using \<open>c \<in> C1\<close> hC1sub by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF hTV hV_conn hV_lpc \<open>V \<noteq> {}\<close>])
  qed
  \<comment> \<open>Subspace topology transitivity.\<close>
  have hU_subtop: "subspace_topology X TX U = subspace_topology top1_S2 top1_S2_topology U"
    unfolding TX_def by (rule subspace_topology_trans[OF hU_sub_X])
  have hV_subtop: "subspace_topology X TX V = subspace_topology top1_S2 top1_S2_topology V"
    unfolding TX_def by (rule subspace_topology_trans[OF hV_sub_X])
  \<comment> \<open>W1, W2, B are subsets of X and open in X.\<close>
  have hW1_sub: "W1 \<subseteq> X" unfolding X_def using assms(18) hpq by (by100 blast)
  have hW2_sub: "W2 \<subseteq> X" unfolding X_def using assms(18) hpq by (by100 blast)
  have hB_sub: "B \<subseteq> X" unfolding X_def using assms(18) hpq by (by100 blast)
  have hW1_open_X: "openin_on X TX W1"
    unfolding openin_on_def TX_def subspace_topology_def using hW1_sub assms(9) by (by100 blast)
  have hW2_open_X: "openin_on X TX W2"
    unfolding openin_on_def TX_def subspace_topology_def using hW2_sub assms(10) by (by100 blast)
  have hB_open_X: "openin_on X TX B"
    unfolding openin_on_def TX_def subspace_topology_def using hB_sub assms(11) by (by100 blast)
  \<comment> \<open>Decomposition 1: A1 = W1\<union>W2, B1 = B.\<close>
  define A1 where "A1 = W1 \<union> W2"
  define B1 where "B1 = B"
  have hA1B1_eq: "U \<inter> V = A1 \<union> B1"
    unfolding A1_def B1_def using hUV_eq assms(18) by (by100 blast)
  have hA1B1_disj: "A1 \<inter> B1 = {}" unfolding A1_def B1_def using assms(16,17) by (by100 blast)
  have hA1_open: "openin_on X TX A1"
  proof -
    have "W1 \<in> TX" using hW1_open_X unfolding openin_on_def by (by100 blast)
    moreover have "W2 \<in> TX" using hW2_open_X unfolding openin_on_def by (by100 blast)
    ultimately have "W1 \<union> W2 \<in> TX" by (rule topology_union2[OF hTX])
    thus ?thesis unfolding A1_def openin_on_def using hW1_sub hW2_sub by (by100 blast)
  qed
  have hB1_open: "openin_on X TX B1" unfolding B1_def using hB_open_X by (by100 simp)
  \<comment> \<open>Pick points.\<close>
  obtain a where ha: "a \<in> W1" using assms(12) by (by100 blast)
  obtain b where hb: "b \<in> B" using assms(14) by (by100 blast)
  have ha_A1: "a \<in> A1" unfolding A1_def using ha by (by100 blast)
  have hb_B1: "b \<in> B1" unfolding B1_def using hb by (by100 simp)
  have ha_U: "a \<in> U" unfolding U_def using ha assms(18) by (by100 blast)
  have hb_U: "b \<in> U" unfolding U_def using hb assms(18) by (by100 blast)
  have ha_V: "a \<in> V" unfolding V_def using ha assms(18) by (by100 blast)
  have hb_V: "b \<in> V" unfolding V_def using hb assms(18) by (by100 blast)
  \<comment> \<open>Paths.\<close>
  obtain \<alpha> where h\<alpha>: "top1_is_path_on U (subspace_topology top1_S2 top1_S2_topology U) a b \<alpha>"
    using hU_pc ha_U hb_U unfolding top1_path_connected_on_def by (by100 blast)
  obtain \<beta> where h\<beta>: "top1_is_path_on V (subspace_topology top1_S2 top1_S2_topology V) b a \<beta>"
    using hV_pc hb_V ha_V unfolding top1_path_connected_on_def by (by100 blast)
  have h\<alpha>_X: "top1_is_path_on U (subspace_topology X TX U) a b \<alpha>"
    using h\<alpha> hU_subtop by (by100 simp)
  have h\<beta>_X: "top1_is_path_on V (subspace_topology X TX V) b a \<beta>"
    using h\<beta> hV_subtop by (by100 simp)
  have hf_nontrivial: "\<not> top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    by (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open hV_open hX_eq
        hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1 h\<alpha>_X h\<beta>_X])
  \<comment> \<open>Decomposition 2: A2 = W1, B2 = W2\<union>B.\<close>
  obtain a' where ha': "a' \<in> W2" using assms(13) by (by100 blast)
  have ha'_U: "a' \<in> U" unfolding U_def using ha' assms(18) by (by100 blast)
  have ha'_V: "a' \<in> V" unfolding V_def using ha' assms(18) by (by100 blast)
  obtain \<gamma> where h\<gamma>: "top1_is_path_on U (subspace_topology top1_S2 top1_S2_topology U) a a' \<gamma>"
    using hU_pc ha_U ha'_U unfolding top1_path_connected_on_def by (by100 blast)
  obtain \<delta> where h\<delta>: "top1_is_path_on V (subspace_topology top1_S2 top1_S2_topology V) a' a \<delta>"
    using hV_pc ha'_V ha_V unfolding top1_path_connected_on_def by (by100 blast)
  have h\<gamma>_X: "top1_is_path_on U (subspace_topology X TX U) a a' \<gamma>"
    using h\<gamma> hU_subtop by (by100 simp)
  have h\<delta>_X: "top1_is_path_on V (subspace_topology X TX V) a' a \<delta>"
    using h\<delta> hV_subtop by (by100 simp)
  define A2 where "A2 = W1"
  define B2 where "B2 = W2 \<union> B"
  have hA2B2_eq: "U \<inter> V = A2 \<union> B2"
    unfolding A2_def B2_def using hUV_eq assms(18) by (by100 blast)
  have hA2B2_disj: "A2 \<inter> B2 = {}" unfolding A2_def B2_def using assms(15,16) by (by100 blast)
  have hA2_open: "openin_on X TX A2" unfolding A2_def using hW1_open_X by (by100 simp)
  have hB2_open: "openin_on X TX B2"
  proof -
    have "W2 \<in> TX" using hW2_open_X unfolding openin_on_def by (by100 blast)
    moreover have "B \<in> TX" using hB_open_X unfolding openin_on_def by (by100 blast)
    ultimately have "W2 \<union> B \<in> TX" by (rule topology_union2[OF hTX])
    thus ?thesis unfolding B2_def openin_on_def using hW2_sub hB_sub by (by100 blast)
  qed
  have ha_A2: "a \<in> A2" unfolding A2_def using ha by (by100 simp)
  have ha'_B2: "a' \<in> B2" unfolding B2_def using ha' by (by100 blast)
  have hg_nontrivial: "\<not> top1_path_homotopic_on X TX a a
      (top1_path_product \<gamma> \<delta>) (top1_constant_path a)"
    by (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open hV_open hX_eq
        hA2B2_eq hA2B2_disj hA2_open hB2_open ha_A2 ha'_B2 h\<gamma>_X h\<delta>_X])
  \<comment> \<open>Loops in X.\<close>
  have h_path_U_to_X: "\<And>a' b' f. top1_is_path_on U (subspace_topology X TX U) a' b' f
      \<Longrightarrow> top1_is_path_on X TX a' b' f"
    using path_in_subspace_is_path_in_space[OF hTX hU_sub_X hU_open] by (by100 blast)
  have h_path_V_to_X: "\<And>a' b' f. top1_is_path_on V (subspace_topology X TX V) a' b' f
      \<Longrightarrow> top1_is_path_on X TX a' b' f"
    using path_in_subspace_is_path_in_space[OF hTX hV_sub_X hV_open] by (by100 blast)
  have hf_loop: "top1_is_loop_on X TX a (top1_path_product \<alpha> \<beta>)"
    unfolding top1_is_loop_on_def
    using top1_path_product_is_path[OF hTX h_path_U_to_X[OF h\<alpha>_X] h_path_V_to_X[OF h\<beta>_X]]
    by (by100 blast)
  have hg_loop: "top1_is_loop_on X TX a (top1_path_product \<gamma> \<delta>)"
    unfolding top1_is_loop_on_def
    using top1_path_product_is_path[OF hTX h_path_U_to_X[OF h\<gamma>_X] h_path_V_to_X[OF h\<delta>_X]]
    by (by100 blast)
  \<comment> \<open>\<pi>_1(X) \<cong> Z \<Rightarrow> common power.\<close>
  have hpi1_cyclic: "\<exists>gen. top1_is_loop_on X TX a gen \<and>
      (\<forall>h. top1_is_loop_on X TX a h \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on X TX a a h (top1_path_power gen a n) \<or>
         top1_path_homotopic_on X TX a a h (top1_path_power (top1_path_reverse gen) a n)))"
  proof -
    have "a \<in> X" using ha hW1_sub by (by100 blast)
    thus ?thesis unfolding X_def TX_def
      by (rule pi1_S2_minus_two_points_infinite_cyclic[OF assms(1) hp_S2 hq_S2 hpq_ne])
  qed
  obtain m k where hm: "m > 0" and hmk:
      "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
        (top1_path_power (top1_path_product \<gamma> \<delta>) a k) \<or>
       top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
        (top1_path_power (top1_path_reverse (top1_path_product \<gamma> \<delta>)) a k)"
    using infinite_cyclic_common_power[OF hTX hf_loop hg_loop
      hf_nontrivial hg_nontrivial hpi1_cyclic] by (by100 blast)
  have ha'_A1: "a' \<in> A1" unfolding A1_def using ha' by (by100 blast)
  have "m = 0" using hmk
  proof
    assume hmk1: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
        (top1_path_power (top1_path_product \<gamma> \<delta>) a k)"
    show "m = 0"
      by (rule Theorem_63_1_c_subgroups_trivial[OF hTX hU_open hV_open hX_eq
        hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1
        h\<alpha>_X h\<beta>_X ha'_A1 h\<gamma>_X h\<delta>_X hmk1])
  next
    assume hmk2: "top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
        (top1_path_power (top1_path_reverse (top1_path_product \<gamma> \<delta>)) a k)"
    show "m = 0"
      by (rule Theorem_63_1_c_subgroups_trivial_reverse[OF hTX hU_open hV_open hX_eq
        hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1
        h\<alpha>_X h\<beta>_X ha'_A1 h\<gamma>_X h\<delta>_X hmk2])
  qed
  thus False using hm by (by100 simp)
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
  \<comment> \<open>At least two components: hsep gives S^2-(C1\<union>C2) disconnected.\<close>
  have hC1sub: "C1 \<subseteq> top1_S2" using assms(2) unfolding closedin_on_def by blast
  have hC2sub: "C2 \<subseteq> top1_S2" using assms(3) unfolding closedin_on_def by blast
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hC_closed: "closedin_on top1_S2 top1_S2_topology (C1 \<union> C2)"
  proof -
    have "C1 \<union> C2 \<subseteq> top1_S2" using hC1sub hC2sub by (by100 blast)
    have "top1_S2 - C1 \<in> top1_S2_topology"
      using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
    have "top1_S2 - C2 \<in> top1_S2_topology"
      using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
    have "top1_S2 - (C1 \<union> C2) = (top1_S2 - C1) \<inter> (top1_S2 - C2)" by (by100 blast)
    hence "top1_S2 - (C1 \<union> C2) \<in> top1_S2_topology"
      using topology_inter_open[OF hTS2 \<open>top1_S2 - C1 \<in> _\<close> \<open>top1_S2 - C2 \<in> _\<close>] by simp
    thus ?thesis using \<open>C1 \<union> C2 \<subseteq> top1_S2\<close> unfolding closedin_on_def by (by100 blast)
  qed
  \<comment> \<open>S^2-(C1\<union>C2) open in S^2, hence locally path-connected. Components = path components.\<close>
  have hopen: "top1_S2 - (C1 \<union> C2) \<in> top1_S2_topology"
    using hC_closed hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  have hlpc: "top1_locally_path_connected_on (top1_S2 - (C1 \<union> C2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hopen]) (by100 blast)
  \<comment> \<open>Step 1: Extract intersection points.\<close>
  obtain p q where hpq: "C1 \<inter> C2 = {p, q}" and hpq_ne: "p \<noteq> q"
    using assms(6) card_2_iff by (by100 metis)
  have hp_S2: "p \<in> top1_S2" using hpq hC1sub by (by100 blast)
  have hq_S2: "q \<in> top1_S2" using hpq hC1sub by (by100 blast)
  \<comment> \<open>Step 2: S^2-C1 and S^2-C2 are path-connected (non-separation + lpc).\<close>
  have hU_pc: "top1_path_connected_on (top1_S2 - C1)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1))"
  proof -
    have hU_conn: "top1_connected_on (top1_S2 - C1)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1))"
      using assms(7) unfolding top1_separates_on_def by (by100 blast)
    have hU_open: "top1_S2 - C1 \<in> top1_S2_topology"
      using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
    have hU_lpc: "top1_locally_path_connected_on (top1_S2 - C1)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1))"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hU_open])
         (by100 blast)
    have hTU: "is_topology_on (top1_S2 - C1)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C1))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    have "top1_S2 - C1 \<noteq> {}"
    proof -
      \<comment> \<open>C2 \<noteq> {p,q}: if C2 = {p,q}, singletons open in Hausdorff subspace \<Rightarrow> disconnected.\<close>
      have "C2 \<noteq> {p, q}"
      proof
        assume "C2 = {p, q}"
        have "{p} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {q} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hq_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{p} = {p, q} \<inter> (top1_S2 - {q})" using hpq_ne hp_S2 by auto
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "{q} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {p} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hp_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{q} = {p, q} \<inter> (top1_S2 - {p})" using hpq_ne hq_S2 by auto
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<not> top1_connected_on {p, q} (subspace_topology top1_S2 top1_S2_topology {p, q})"
          unfolding top1_connected_on_def
          using \<open>{p} \<in> _\<close> \<open>{q} \<in> _\<close> hpq_ne by (by100 blast)
        thus False using assms(5) \<open>C2 = {p, q}\<close> by simp
      qed
      moreover have "{p, q} \<subseteq> C2" using hpq by (by100 blast)
      ultimately obtain c where "c \<in> C2" "c \<notin> {p, q}"
        by (by100 blast)
      hence "c \<notin> C1" using hpq by (by100 blast)
      hence "c \<in> top1_S2 - C1" using \<open>c \<in> C2\<close> hC2sub by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF
        hTU hU_conn hU_lpc \<open>top1_S2 - C1 \<noteq> {}\<close>])
  qed
  have hV_pc: "top1_path_connected_on (top1_S2 - C2)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2))"
  proof -
    have hV_conn: "top1_connected_on (top1_S2 - C2)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2))"
      using assms(8) unfolding top1_separates_on_def by (by100 blast)
    have hV_open: "top1_S2 - C2 \<in> top1_S2_topology"
      using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
    have hV_lpc: "top1_locally_path_connected_on (top1_S2 - C2)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2))"
      by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hV_open])
         (by100 blast)
    have hTV: "is_topology_on (top1_S2 - C2)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C2))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    have "top1_S2 - C2 \<noteq> {}"
    proof -
      have "C1 \<noteq> {p, q}"
      proof
        assume "C1 = {p, q}"
        have "{p} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {q} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hq_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{p} = {p, q} \<inter> (top1_S2 - {q})" using hpq_ne hp_S2 by auto
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "{q} \<in> subspace_topology top1_S2 top1_S2_topology {p, q}"
        proof -
          have "top1_S2 - {p} \<in> top1_S2_topology"
            using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hp_S2]
            hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          moreover have "{q} = {p, q} \<inter> (top1_S2 - {p})" using hpq_ne hq_S2 by auto
          ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
        qed
        have "\<not> top1_connected_on {p, q} (subspace_topology top1_S2 top1_S2_topology {p, q})"
          unfolding top1_connected_on_def
          using \<open>{p} \<in> _\<close> \<open>{q} \<in> _\<close> hpq_ne by (by100 blast)
        thus False using assms(4) \<open>C1 = {p, q}\<close> by simp
      qed
      moreover have "{p, q} \<subseteq> C1" using hpq by (by100 blast)
      ultimately obtain c where "c \<in> C1" "c \<notin> {p, q}"
        by (by100 blast)
      hence "c \<notin> C2" using hpq by (by100 blast)
      hence "c \<in> top1_S2 - C2" using \<open>c \<in> C1\<close> hC1sub by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF
        hTV hV_conn hV_lpc \<open>top1_S2 - C2 \<noteq> {}\<close>])
  qed
  \<comment> \<open>Step 3: Exactly 2 components. \<ge>2 from hsep. \<le>2 needs 63.1(c) + \<pi>_1 \<cong> Z.\<close>
  \<comment> \<open>From \<not> connected, extract a separation into two nonempty open sets.\<close>
  have h_not_conn: "\<not> top1_connected_on (top1_S2 - (C1 \<union> C2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2)))"
    using hsep unfolding top1_separates_on_def by simp
  have hTsub: "is_topology_on (top1_S2 - (C1 \<union> C2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2)))"
    by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
  obtain W1 R where hW1R: "W1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2))"
      "R \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (C1 \<union> C2))"
      "W1 \<noteq> {}" "R \<noteq> {}" "W1 \<inter> R = {}" "W1 \<union> R = top1_S2 - (C1 \<union> C2)"
    using h_not_conn hTsub unfolding top1_connected_on_def by blast
  \<comment> \<open>Key claim: R is connected. If not, S^2-(C1\<union>C2) has \<ge>3 components, contradiction.\<close>
  have hR_conn: "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
  proof (rule ccontr)
    assume "\<not> top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
    \<comment> \<open>R is open in S^2 (it's open in the open subspace S^2-(C1\<union>C2)).\<close>
    have hR_sub: "R \<subseteq> top1_S2 - (C1 \<union> C2)" using hW1R(6) by (by100 blast)
    have hR_open_S2: "R \<in> top1_S2_topology"
    proof -
      obtain W where "W \<in> top1_S2_topology" "R = (top1_S2 - (C1 \<union> C2)) \<inter> W"
        using hW1R(2) unfolding subspace_topology_def by (by100 blast)
      hence "R = W \<inter> (top1_S2 - (C1 \<union> C2))" by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 \<open>W \<in> _\<close> hopen] by simp
    qed
    have hW1_open_S2: "W1 \<in> top1_S2_topology"
    proof -
      obtain W where "W \<in> top1_S2_topology" "W1 = (top1_S2 - (C1 \<union> C2)) \<inter> W"
        using hW1R(1) unfolding subspace_topology_def by (by100 blast)
      hence "W1 = W \<inter> (top1_S2 - (C1 \<union> C2))" by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 \<open>W \<in> _\<close> hopen] by simp
    qed
    have hTR: "is_topology_on R (subspace_topology top1_S2 top1_S2_topology R)"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (use hR_sub hC1sub hC2sub in blast)
    obtain W2 B where hW2B: "W2 \<in> subspace_topology top1_S2 top1_S2_topology R"
        "B \<in> subspace_topology top1_S2 top1_S2_topology R"
        "W2 \<noteq> {}" "B \<noteq> {}" "W2 \<inter> B = {}" "W2 \<union> B = R"
      using \<open>\<not> top1_connected_on R _\<close> hTR unfolding top1_connected_on_def by blast
    \<comment> \<open>Now W1, W2, B are 3 disjoint nonempty open sets covering S^2-(C1\<union>C2).\<close>
    have hW2_sub: "W2 \<subseteq> top1_S2 - (C1 \<union> C2)" using hW2B(6) hR_sub by (by100 blast)
    have hB_sub: "B \<subseteq> top1_S2 - (C1 \<union> C2)" using hW2B(6) hR_sub by (by100 blast)
    have hW1_sub: "W1 \<subseteq> top1_S2 - (C1 \<union> C2)" using hW1R(6) by (by100 blast)
    have hW2_open_S2: "W2 \<in> top1_S2_topology"
    proof -
      obtain W where hW: "W \<in> top1_S2_topology" "W2 = R \<inter> W"
        using hW2B(1) unfolding subspace_topology_def by (by100 blast)
      have "R \<inter> W = W \<inter> R" by (by100 blast)
      hence "W2 = W \<inter> R" using hW(2) by simp
      thus ?thesis using topology_inter_open[OF hTS2 hW(1) hR_open_S2] by simp
    qed
    have hB_open_S2: "B \<in> top1_S2_topology"
    proof -
      obtain W where hW: "W \<in> top1_S2_topology" "B = R \<inter> W"
        using hW2B(2) unfolding subspace_topology_def by (by100 blast)
      have "R \<inter> W = W \<inter> R" by (by100 blast)
      hence "B = W \<inter> R" using hW(2) by simp
      thus ?thesis using topology_inter_open[OF hTS2 hW(1) hR_open_S2] by simp
    qed
    have h3_disj: "W1 \<inter> W2 = {}" "W1 \<inter> B = {}" "W2 \<inter> B = {}"
      using hW1R(5) hW2B(5,6) by (by100 blast)+
    have h3_cover: "W1 \<union> W2 \<union> B = top1_S2 - (C1 \<union> C2)"
      using hW1R(6) hW2B(6) by (by100 blast)
    \<comment> \<open>Set up 63.1 framework: X = S^2-{p,q}, U' = S^2-C1, V' = S^2-C2.
       U' \<inter> V' = S^2-(C1\<union>C2). Decompose as A\<union>B in two ways:
       Way 1: A1 = W1\<union>W2, B1 = B.  Way 2: A2 = W1, B2 = W2\<union>B.\<close>
    let ?X = "top1_S2 - {p} - {q}"
    let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
    let ?U = "top1_S2 - C1"
    let ?V = "top1_S2 - C2"
    have hX_eq: "?U \<union> ?V = ?X"
    proof -
      have "?U \<union> ?V = top1_S2 - (C1 \<inter> C2)" by (by100 blast)
      also have "... = top1_S2 - {p, q}" using hpq by simp
      also have "... = ?X" by (by100 blast)
      finally show ?thesis .
    qed
    have hUV_eq: "?U \<inter> ?V = top1_S2 - (C1 \<union> C2)" by (by100 blast)
    have hTX: "is_topology_on ?X ?TX"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
    have hU_open: "openin_on ?X ?TX ?U"
    proof -
      have "?U \<in> top1_S2_topology"
        using assms(2) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have "?U \<subseteq> ?X" using hpq hC1sub by (by100 blast)
      have "?U \<in> ?TX" unfolding subspace_topology_def using \<open>?U \<in> _\<close> \<open>?U \<subseteq> ?X\<close> by (by100 blast)
      thus ?thesis unfolding openin_on_def using \<open>?U \<subseteq> ?X\<close> by (by100 blast)
    qed
    have hV_open: "openin_on ?X ?TX ?V"
    proof -
      have "?V \<in> top1_S2_topology"
        using assms(3) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have "?V \<subseteq> ?X" using hpq hC2sub by (by100 blast)
      have "?V \<in> ?TX" unfolding subspace_topology_def using \<open>?V \<in> _\<close> \<open>?V \<subseteq> ?X\<close> by (by100 blast)
      thus ?thesis unfolding openin_on_def using \<open>?V \<subseteq> ?X\<close> by (by100 blast)
    qed
    \<comment> \<open>Subspace topology transitivity: U \<subseteq> X \<subseteq> S^2, so subspace of X on U = subspace of S^2 on U.\<close>
    have hU_sub_X: "?U \<subseteq> ?X" using hpq hC1sub by (by100 blast)
    have hV_sub_X: "?V \<subseteq> ?X" using hpq hC2sub by (by100 blast)
    have hU_subtop: "subspace_topology ?X ?TX ?U = subspace_topology top1_S2 top1_S2_topology ?U"
      by (rule subspace_topology_trans[OF hU_sub_X])
    have hV_subtop: "subspace_topology ?X ?TX ?V = subspace_topology top1_S2 top1_S2_topology ?V"
      by (rule subspace_topology_trans[OF hV_sub_X])
    \<comment> \<open>All three sets are open in X (they're open in S^2 and contained in X).\<close>
    have hW1_X: "W1 \<subseteq> ?X" using hW1_sub hpq by (by100 blast)
    have hW2_X: "W2 \<subseteq> ?X" using hW2_sub hpq by (by100 blast)
    have hB_X: "B \<subseteq> ?X" using hB_sub hpq by (by100 blast)
    have hW1_open_X: "openin_on ?X ?TX W1"
      unfolding openin_on_def using hW1_X hW1_open_S2
      unfolding subspace_topology_def by (by100 blast)
    have hW2_open_X: "openin_on ?X ?TX W2"
      unfolding openin_on_def using hW2_X hW2_open_S2
      unfolding subspace_topology_def by (by100 blast)
    have hB_open_X: "openin_on ?X ?TX B"
      unfolding openin_on_def using hB_X hB_open_S2
      unfolding subspace_topology_def by (by100 blast)
    \<comment> \<open>Decomposition 1: A1 = W1\<union>W2, B1 = B for loop f = \<alpha>*\<beta>.\<close>
    define A1 where "A1 = W1 \<union> W2"
    define B1 where "B1 = B"
    have hA1B1_eq: "?U \<inter> ?V = A1 \<union> B1"
    proof -
      have "A1 \<union> B1 = W1 \<union> W2 \<union> B" unfolding A1_def B1_def by (by100 blast)
      also have "... = top1_S2 - (C1 \<union> C2)" using h3_cover by simp
      also have "... = ?U \<inter> ?V" using hUV_eq by simp
      finally show ?thesis by simp
    qed
    have hA1B1_disj: "A1 \<inter> B1 = {}" unfolding A1_def B1_def
      using h3_disj by (by100 blast)
    have hA1_open: "openin_on ?X ?TX A1"
    proof -
      have hW1T: "W1 \<in> ?TX" using hW1_open_X unfolding openin_on_def by (by100 blast)
      have hW2T: "W2 \<in> ?TX" using hW2_open_X unfolding openin_on_def by (by100 blast)
      have "W1 \<union> W2 \<in> ?TX" by (rule topology_union2[OF hTX hW1T hW2T])
      thus ?thesis unfolding A1_def openin_on_def using hW1_X hW2_X by (by100 blast)
    qed
    have hB1_open: "openin_on ?X ?TX B1" unfolding B1_def using hB_open_X by simp
    \<comment> \<open>Pick a \<in> W1 \<subseteq> A1 and b \<in> B1 = B.\<close>
    obtain a where ha: "a \<in> W1" using hW1R(3) by (by100 blast)
    obtain b where hb: "b \<in> B" using hW2B(4) by (by100 blast)
    have ha_A1: "a \<in> A1" unfolding A1_def using ha by (by100 blast)
    have hb_B1: "b \<in> B1" unfolding B1_def using hb by simp
    have ha_X: "a \<in> ?X" using ha hW1_X by (by100 blast)
    have hb_X: "b \<in> ?X" using hb hB_X by (by100 blast)
    \<comment> \<open>Paths: \<alpha> from a to b in U (= S^2-C1), \<beta> from b to a in V (= S^2-C2).
       These exist because U and V are path-connected.\<close>
    have ha_U: "a \<in> ?U" using ha hW1_sub by (by100 blast)
    have hb_U: "b \<in> ?U" using hb hB_sub by (by100 blast)
    have ha_V: "a \<in> ?V" using ha hW1_sub by (by100 blast)
    have hb_V: "b \<in> ?V" using hb hB_sub by (by100 blast)
    obtain \<alpha> where h\<alpha>: "top1_is_path_on ?U
        (subspace_topology top1_S2 top1_S2_topology ?U) a b \<alpha>"
      using hU_pc ha_U hb_U unfolding top1_path_connected_on_def by (by100 blast)
    obtain \<beta> where h\<beta>: "top1_is_path_on ?V
        (subspace_topology top1_S2 top1_S2_topology ?V) b a \<beta>"
      using hV_pc hb_V ha_V unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>f = \<alpha>*\<beta> is nontrivial by 63.1(a).\<close>
    have hf_nontrivial: "\<not> top1_path_homotopic_on ?X ?TX a a
        (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    proof (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open hV_open hX_eq
        hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1])
      \<comment> \<open>Need paths in subspace of X restricted to U and V.\<close>
      show "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>"
        using h\<alpha> hU_subtop by simp
      show "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>"
        using h\<beta> hV_subtop by simp
    qed
    \<comment> \<open>Decomposition 2: A2 = W1, B2 = W2\<union>B for loop g = \<gamma>*\<delta>.\<close>
    define A2 where "A2 = W1"
    define B2 where "B2 = W2 \<union> B"
    have hA2B2_eq: "?U \<inter> ?V = A2 \<union> B2"
    proof -
      have "A2 \<union> B2 = W1 \<union> (W2 \<union> B)" unfolding A2_def B2_def by (by100 blast)
      also have "... = W1 \<union> W2 \<union> B" by (by100 blast)
      also have "... = top1_S2 - (C1 \<union> C2)" using h3_cover by simp
      also have "... = ?U \<inter> ?V" using hUV_eq by simp
      finally show ?thesis by simp
    qed
    have hA2B2_disj: "A2 \<inter> B2 = {}" unfolding A2_def B2_def
      using h3_disj by (by100 blast)
    have hA2_open: "openin_on ?X ?TX A2" unfolding A2_def using hW1_open_X by simp
    have hB2_open: "openin_on ?X ?TX B2"
    proof -
      have hW2T: "W2 \<in> ?TX" using hW2_open_X unfolding openin_on_def by (by100 blast)
      have hBT: "B \<in> ?TX" using hB_open_X unfolding openin_on_def by (by100 blast)
      have "W2 \<union> B \<in> ?TX" by (rule topology_union2[OF hTX hW2T hBT])
      thus ?thesis unfolding B2_def openin_on_def using hW2_X hB_X by (by100 blast)
    qed
    \<comment> \<open>Pick a \<in> W1 = A2 (same a), a' \<in> W2 \<subseteq> B2.\<close>
    obtain a' where ha': "a' \<in> W2" using hW2B(3) by (by100 blast)
    have ha_A2: "a \<in> A2" unfolding A2_def using ha by simp
    have ha'_B2: "a' \<in> B2" unfolding B2_def using ha' by (by100 blast)
    have ha'_X: "a' \<in> ?X" using ha' hW2_X by (by100 blast)
    have ha'_U: "a' \<in> ?U" using ha' hW2_sub by (by100 blast)
    have ha'_V: "a' \<in> ?V" using ha' hW2_sub by (by100 blast)
    obtain \<gamma> where h\<gamma>: "top1_is_path_on ?U
        (subspace_topology top1_S2 top1_S2_topology ?U) a a' \<gamma>"
      using hU_pc ha_U ha'_U unfolding top1_path_connected_on_def by (by100 blast)
    obtain \<delta> where h\<delta>: "top1_is_path_on ?V
        (subspace_topology top1_S2 top1_S2_topology ?V) a' a \<delta>"
      using hV_pc ha'_V ha_V unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>g = \<gamma>*\<delta> is nontrivial by 63.1(a) with decomposition A2, B2.\<close>
    have hg_nontrivial: "\<not> top1_path_homotopic_on ?X ?TX a a
        (top1_path_product \<gamma> \<delta>) (top1_constant_path a)"
    proof (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open hV_open hX_eq
        hA2B2_eq hA2B2_disj hA2_open hB2_open ha_A2 ha'_B2])
      show "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a a' \<gamma>"
        using h\<gamma> hU_subtop by simp
      show "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) a' a \<delta>"
        using h\<delta> hV_subtop by simp
    qed
    \<comment> \<open>By \<pi>_1(X) \<cong> Z and both [f],[g] nontrivial: \<exists> m>0, k. [f]^m = [g]^k.\<close>
    have h\<alpha>_X: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a b \<alpha>"
      using h\<alpha> hU_subtop by simp
    have h\<beta>_X: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) b a \<beta>"
      using h\<beta> hV_subtop by simp
    have h\<gamma>_X: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a a' \<gamma>"
      using h\<gamma> hU_subtop by simp
    have h\<delta>_X: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) a' a \<delta>"
      using h\<delta> hV_subtop by simp
    \<comment> \<open>Paths in U (or V) restricted to X: since U \<subseteq> X, a path in U is a path in X.\<close>
    have h_path_U_to_X: "\<And>a' b' f. top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a' b' f
        \<Longrightarrow> top1_is_path_on ?X ?TX a' b' f"
    proof -
      fix a' b' f assume hf: "top1_is_path_on ?U (subspace_topology ?X ?TX ?U) a' b' f"
      show "top1_is_path_on ?X ?TX a' b' f"
        unfolding top1_is_path_on_def top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume hs: "s \<in> I_set"
        have "f s \<in> ?U" using hf hs unfolding top1_is_path_on_def top1_continuous_map_on_def
          by (by100 blast)
        thus "f s \<in> ?X" using hU_sub_X by (by100 blast)
      next
        fix W assume hW: "W \<in> ?TX"
        have hUW_sub: "?U \<inter> W \<in> subspace_topology ?X ?TX ?U"
        proof -
          have "?U \<inter> W = ?U \<inter> W" by simp
          moreover have "W \<in> ?TX" by (rule hW)
          ultimately show ?thesis unfolding subspace_topology_def by blast
        qed
        have h_pre: "{s \<in> I_set. f s \<in> ?U \<inter> W} \<in> I_top"
          using hf hUW_sub
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        have h_in_U: "\<forall>s\<in>I_set. f s \<in> ?U"
          using hf unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        have "{s \<in> I_set. f s \<in> W} = {s \<in> I_set. f s \<in> ?U \<inter> W}"
          using h_in_U by (by100 blast)
        thus "{s \<in> I_set. f s \<in> W} \<in> I_top" using h_pre by simp
      next
        show "f 0 = a'" using hf unfolding top1_is_path_on_def by (by100 blast)
      next
        show "f 1 = b'" using hf unfolding top1_is_path_on_def by (by100 blast)
      qed
    qed
    have h_path_V_to_X: "\<And>a' b' f. top1_is_path_on ?V (subspace_topology ?X ?TX ?V) a' b' f
        \<Longrightarrow> top1_is_path_on ?X ?TX a' b' f"
    proof -
      fix a' b' f assume hf: "top1_is_path_on ?V (subspace_topology ?X ?TX ?V) a' b' f"
      show "top1_is_path_on ?X ?TX a' b' f"
        unfolding top1_is_path_on_def top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume hs: "s \<in> I_set"
        have "f s \<in> ?V" using hf hs unfolding top1_is_path_on_def top1_continuous_map_on_def
          by (by100 blast)
        thus "f s \<in> ?X" using hV_sub_X by (by100 blast)
      next
        fix W assume hW: "W \<in> ?TX"
        have hVW_sub: "?V \<inter> W \<in> subspace_topology ?X ?TX ?V"
        proof -
          have "?V \<inter> W = ?V \<inter> W" by simp
          moreover have "W \<in> ?TX" by (rule hW)
          ultimately show ?thesis unfolding subspace_topology_def by blast
        qed
        have h_pre: "{s \<in> I_set. f s \<in> ?V \<inter> W} \<in> I_top"
          using hf hVW_sub
          unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        have h_in_V: "\<forall>s\<in>I_set. f s \<in> ?V"
          using hf unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        have "{s \<in> I_set. f s \<in> W} = {s \<in> I_set. f s \<in> ?V \<inter> W}"
          using h_in_V by (by100 blast)
        thus "{s \<in> I_set. f s \<in> W} \<in> I_top" using h_pre by simp
      next
        show "f 0 = a'" using hf unfolding top1_is_path_on_def by (by100 blast)
      next
        show "f 1 = b'" using hf unfolding top1_is_path_on_def by (by100 blast)
      qed
    qed
    have hf_loop: "top1_is_loop_on ?X ?TX a (top1_path_product \<alpha> \<beta>)"
    proof -
      have h\<alpha>_path_X: "top1_is_path_on ?X ?TX a b \<alpha>" by (rule h_path_U_to_X[OF h\<alpha>_X])
      have h\<beta>_path_X: "top1_is_path_on ?X ?TX b a \<beta>" by (rule h_path_V_to_X[OF h\<beta>_X])
      show ?thesis unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF hTX h\<alpha>_path_X h\<beta>_path_X] by (by100 blast)
    qed
    have hg_loop: "top1_is_loop_on ?X ?TX a (top1_path_product \<gamma> \<delta>)"
    proof -
      have h\<gamma>_path_X: "top1_is_path_on ?X ?TX a a' \<gamma>" by (rule h_path_U_to_X[OF h\<gamma>_X])
      have h\<delta>_path_X: "top1_is_path_on ?X ?TX a' a \<delta>" by (rule h_path_V_to_X[OF h\<delta>_X])
      show ?thesis unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF hTX h\<gamma>_path_X h\<delta>_path_X] by (by100 blast)
    qed
    have hpi1_cyclic: "\<exists>gen. top1_is_loop_on ?X ?TX a gen \<and>
        (\<forall>h. top1_is_loop_on ?X ?TX a h \<longrightarrow>
          (\<exists>n::nat. top1_path_homotopic_on ?X ?TX a a h (top1_path_power gen a n) \<or>
           top1_path_homotopic_on ?X ?TX a a h (top1_path_power (top1_path_reverse gen) a n)))"
    proof -
      have "a \<in> ?X" using ha hW1_X by (by100 blast)
      thus ?thesis by (rule pi1_S2_minus_two_points_infinite_cyclic[OF assms(1) hp_S2 hq_S2 hpq_ne])
    qed
    obtain m k where hm: "m > 0" and hmk:
        "top1_path_homotopic_on ?X ?TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_product \<gamma> \<delta>) a k) \<or>
         top1_path_homotopic_on ?X ?TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_reverse (top1_path_product \<gamma> \<delta>)) a k)"
      using infinite_cyclic_common_power[OF hTX hf_loop hg_loop
        hf_nontrivial hg_nontrivial hpi1_cyclic] by (by100 blast)
    \<comment> \<open>By 63.1(c): m must be 0. But m > 0. Contradiction!\<close>
    \<comment> \<open>For 63.1(c), we use decomposition 1 (A1, B1) for \<alpha>*\<beta>, and a' \<in> A1 for \<gamma>*\<delta>.
       In the reverse case, use \<delta>\<inverse>*\<gamma>\<inverse> instead of \<gamma>*\<delta>, with same 63.1(c).\<close>
    have ha'_A1: "a' \<in> A1" unfolding A1_def using ha' by (by100 blast)
    have "m = 0" using hmk
    proof
      assume hmk1: "top1_path_homotopic_on ?X ?TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_product \<gamma> \<delta>) a k)"
      show "m = 0"
        by (rule Theorem_63_1_c_subgroups_trivial[OF hTX hU_open hV_open hX_eq
          hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1
          h\<alpha>_X h\<beta>_X ha'_A1 h\<gamma>_X h\<delta>_X hmk1])
    next
      assume hmk2: "top1_path_homotopic_on ?X ?TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_reverse (top1_path_product \<gamma> \<delta>)) a k)"
      \<comment> \<open>g\<inverse> = (\<gamma>*\<delta>)\<inverse> = \<delta>\<inverse>*\<gamma>\<inverse>: path from a to a' (reversed) in V then U.
         Apply 63.1(c) with \<gamma>' = \<delta>\<inverse> (in V from a to a') and \<delta>' = \<gamma>\<inverse> (in U from a' to a).
         Note: a' \<in> A1, same decomposition. Need paths in correct subspaces.\<close>
      show "m = 0"
        by (rule Theorem_63_1_c_subgroups_trivial_reverse[OF hTX hU_open hV_open hX_eq
          hA1B1_eq hA1B1_disj hA1_open hB1_open ha_A1 hb_B1
          h\<alpha>_X h\<beta>_X ha'_A1 h\<gamma>_X h\<delta>_X hmk2])
    qed
    thus False using hm by simp
  qed
  \<comment> \<open>Now construct the two connected components.\<close>
  have hW1_conn: "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
  proof (rule ccontr)
    assume "\<not> top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
    \<comment> \<open>Symmetric to hR_conn: W1 splits into W1a, W1b, giving 3 components {W1a, W1b, R}.\<close>
    have hW1_open_S2: "W1 \<in> top1_S2_topology"
    proof -
      obtain W where "W \<in> top1_S2_topology" "W1 = (top1_S2 - (C1 \<union> C2)) \<inter> W"
        using hW1R(1) unfolding subspace_topology_def by (by100 blast)
      hence "W1 = W \<inter> (top1_S2 - (C1 \<union> C2))" by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 \<open>W \<in> _\<close> hopen] by simp
    qed
    have hTW1: "is_topology_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
      by (rule subspace_topology_is_topology_on[OF hTS2]) (use hW1R(6) in blast)
    obtain W1a W1b where hWab: "W1a \<in> subspace_topology top1_S2 top1_S2_topology W1"
        "W1b \<in> subspace_topology top1_S2 top1_S2_topology W1"
        "W1a \<noteq> {}" "W1b \<noteq> {}" "W1a \<inter> W1b = {}" "W1a \<union> W1b = W1"
      using \<open>\<not> top1_connected_on W1 _\<close> hTW1 unfolding top1_connected_on_def by blast
    \<comment> \<open>W1a, W1b are open in S^2 (open in open set = open).\<close>
    have hW1a_open_S2: "W1a \<in> top1_S2_topology"
    proof -
      obtain V where hV: "V \<in> top1_S2_topology" "W1a = W1 \<inter> V"
        using hWab(1) unfolding subspace_topology_def by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 hW1_open_S2 hV(1)] by (by100 blast)
    qed
    have hW1b_open_S2: "W1b \<in> top1_S2_topology"
    proof -
      obtain V where hV: "V \<in> top1_S2_topology" "W1b = W1 \<inter> V"
        using hWab(2) unfolding subspace_topology_def by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 hW1_open_S2 hV(1)] by (by100 blast)
    qed
    have hR_open_S2: "R \<in> top1_S2_topology"
    proof -
      obtain V where "V \<in> top1_S2_topology" "R = (top1_S2 - (C1 \<union> C2)) \<inter> V"
        using hW1R(2) unfolding subspace_topology_def by (by100 blast)
      hence "R = V \<inter> (top1_S2 - (C1 \<union> C2))" by (by100 blast)
      thus ?thesis using topology_inter_open[OF hTS2 \<open>V \<in> _\<close> hopen] by simp
    qed
    have h3_disj: "W1a \<inter> W1b = {}" "W1a \<inter> R = {}" "W1b \<inter> R = {}"
      using hWab(5,6) hW1R(5) by (by100 blast)+
    have h3_cover: "W1a \<union> W1b \<union> R = top1_S2 - (C1 \<union> C2)"
      using hWab(6) hW1R(6) by (by100 blast)
    have hR_ne: "R \<noteq> {}" by (rule hW1R(4))
    show False by (rule three_components_contradiction[OF assms(1-8)
        hW1a_open_S2 hW1b_open_S2 hR_open_S2 hWab(3,4) hR_ne h3_disj h3_cover])
  qed
  show ?thesis
  proof (intro exI conjI)
    show "W1 \<noteq> {}" by (rule hW1R(3))
    show "R \<noteq> {}" by (rule hW1R(4))
    show "W1 \<inter> R = {}" by (rule hW1R(5))
    show "W1 \<union> R = top1_S2 - (C1 \<union> C2)" by (rule hW1R(6))
    show "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
      by (rule hW1_conn)
    show "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
      by (rule hR_conn)
  qed
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

