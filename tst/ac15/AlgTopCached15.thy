theory AlgTopCached15
  imports "AlgTopCached14.AlgTopCached14"
begin

\<comment> \<open>SORRY ANALYSIS (as of 2026-06-14, sessions 1316-1511, 18 standalone sorry lines):
UPDATE (session 1501-1511):
- h\\_psi\\_e\\_int: PROVED (boundary image extraction from polygon\\_homeomorphic\\_to\\_disk)
- p\\_cm interior: PROVED (fst(p\\_cm)²+snd(p\\_cm)² < 1)
- h\\_tau\\_strict\\_B2: BOTH sectors FULLY PROVED (good + cancel, zero sorry)
- h\\_tau\\_cancel\\_bdy: FULLY PROVED (\\<tau> at cancel boundary maps to B2 interior)
- h\\_tau\\_vtx1\\_int: PROVED (\\<tau>(\\<psi>\\_e(vertex\\_e(1))) in B2 interior)
- converse vtx\\_id \\<subseteq> output\\_step\\_rel: PROVED (symmetry swap)
- BUG FOUND AND FIXED: h\\_tau\\_inj was FALSE (midpoint ray collapse when p\\_cm=0).
  Fix: changed spur target from centroid to midpoint(vertex\\_m(0), centroid).
  p\\_cm \\<noteq> (0,0) now provable (modulo PolygonDisk export blocked by eta-conversion).
- hspur\\_in\\_Pm: PROVED (spur target in P\\_m via coefficient averaging)
- Remaining \\<tau> fix sorrys: hspur\\_interior (cross product, ~100 lines), \\<psi>\\_m(centroid)=(0,0) (eta issue).

SPUR COLLAPSE (decomposed, key properties proved):
- h\\_tau\\_range: FULLY PROVED!
- h\\_tau\\_surj: FULLY PROVED!
- h\\_tau\\_cont: PROVED from sub-sorrys via continuous\\_on\\_closed\\_Un pasting:
  (1) S\\_g closed — PROVED \\<checkmark>
  (2) S\\_c closed — PROVED \\<checkmark>
  (3+4) Nonzero continuity: consolidated to h\\_tau\\_cont\\_B2\\_nonzero via continuous\\_on\\_subset.
    Decomposed via open cover U1={snd>0}\\<union>{fst<0}, U2={snd<0}\\<union>{fst>0} + at\\_within\\_nhd.
    2 sorrys: h\\_U1\\_cont (angle continuous, cases\\_le), h\\_U2\\_cont (closed paste).
  Bounds |fst/snd(\\<tau>)| \\<le> C*r: ALL 4 PROVED (triangle ineq + convex comb bound)
- h\\_spur\\_good\\_edge: FULLY PROVED!
- h\\_spur\\_cancel\\_collapse: FULLY PROVED!
- h\\_spur\\_vertex: FULLY PROVED! (k\\<ge>2 \\<to> vx\\_m(k-2))
- h\\_spur\\_vertex\\_0: FULLY PROVED! (vx\\_e(0) \\<to> vx\\_m(0))
- h\\_fibres\\_good\\_edge: FULLY PROVED!
- h\\_fibres: PROVED from forward + backward.
  h\\_fibres\\_forward: FULLY PROVED (ZERO SORRY)!
    Interior: C8\\_e. Good-good: C9+shift+C7. Cancel-cancel: collapse+dir.
    Cancel-good: freshness contradiction. Vertex-edge: hC12\\_e contradiction.
    Vertex-vertex: PROVED via rtrancl chain transfer:
      scheme\\_quotient\\_exists exports vtgt\\<to>rtrancl (PROVED).
      h\\_step\\_f: each C7 generator preserves q\\_m\\<circ>spur\\_f (PROVED).
      h\\_rtrancl\\_f: closure preserves f (PROVED by rtrancl\\_induct).
      h\\_vtx\\_vtgt\\_transfer: vtgt equality \\<to> f equality (PROVED).
  h\\_fibres\\_backward: sorry (similar case analysis to forward).
- hC12\\_e, hC12\\_m: BOTH PROVED from scheme\\_quotient\\_exists(2).
- scheme\\_quotient\\_exists: BOTH conclusions FULLY PROVED (zero sorry).
  (2) outputs ALL C1-C12 + vtgt facts + vtgt(k) \\<le> k + vtgt idempotent + rtrancl characterization.
- edge\\_interior\\_not\\_vertex: PROVED (polygon-level, C3+C11).

CUT-PASTE (5 sorrys):
- Same-space (3): quotient\\_of\\_scheme\\_cut\\_paste/2/opp (lines 113, 125, 153)
- Proper variants (2): cut-reglue homeo between canonical quotients (lines 4350, 4399)
  Structural proof done: canonical quotients + bridge + transfer. Only cut-reglue sorry.

VERTEX UNIQUENESS (5 sorrys, decomposed from 2):
- Forward: vertex-vertex (1), vertex-edge-interior (2) — lines 4219, 4226, 4314
- Backward: vertex case (1) — line 4427
  Vertex extraction infrastructure PROVED (phi maps vx1(k) to vx2(k)).

GENUINELY FALSE (2 sorrys): length(u@v) < 3 after cancel — lines 5376, 5543
  Fix: add length precondition (requires cached session change)

CONTEXT-LEFT (10 sorrys): suffix operations \\<noteq> full-scheme operations — lines 5624-5782
  PROVED: v\\_relabel(fresh), v\\_cancel(long), v\\_uncancel, v\\_cancel\\_reverse,
          v\\_cut\\_paste, v\\_cut\\_paste\\_opp, v\\_flip\\_label(fresh).
  SORRY: v\\_rotate(inner), v\\_invert(inner), v\\_flip\\_label(non-fresh),
         v\\_cut\\_paste\\_reverse, v\\_cut\\_paste2, v\\_context\\_left(recursive).

CUT-PASTE REVERSE (2 sorrys): lines 5409, 5416
  Need reverse of cut-paste geometry.

FINAL ASSEMBLY (3 sorrys):
- Thm 78.2 induction (line 6666): polygon-pasting
- Scheme extraction (line 6707): construct scheme from quotient map
- Sphere realization (line 6749): sphere scheme quotient \\<cong> S2

DEAD CODE (1 sorry): Theorem\\_76 relabel (line 5849)

KEY INFRASTRUCTURE (all PROVED):
- scheme\\_quotient\\_exists, scheme\\_quotient\\_uniqueness, compact\\_surj\\_quotient
- scheme\\_quotient\\_transfer\\_along\\_homeomorphism (all 11 conditions)
- front\\_cancel\\_proper skeleton (modulo spur collapse sub-sorrys)
- quotient\\_of\\_scheme\\_uncancel\\_front\\_proper (for proper schemes)
- spur\\_f = \\<psi>\\_m\\<inverse> \\<circ> \\<tau> \\<circ> \\<psi>\\_e continuity + surjectivity (from sub-sorrys)
- Continuity chain: \\<psi>\\_e \\<checkmark> \\<to> \\<tau> (sorry) \\<to> \\<psi>\\_m\\<inverse> \\<checkmark> \\<to> spur\\_f \\<checkmark>
- Vertex extraction: \\<phi>(vx1(k)) = vx2(k) for k < n
- r > 0, r \\<le> 1, r^2 = fst p^2 + snd p^2 (for \\<tau> range proof)
- real\\_abs\\_mul\\_le\\_half\\_sum\\_squares: |xy| \\<le> (x^2+y^2)/2 (AM-GM global)
- real\\_inner2\\_abs\\_le\\_half\\_norm\\_sums: |s\\<cdot>d| \\<le> (S+D)/2 (2D inner product bound)
- cancel\\_shift\\_label: ([a,a\\<inverse>]@w)!(i+2) = w!i (index shift for fibre matching)\<close>

\<comment> \<open>valid\\_operation\\_reverse, valid\\_equiv\\_sym: cached in AlgTopCached14.\<close>
\<comment> \<open>§77 normal form chain (scheme\\_normal\\_form\\_valid + all valid helpers): cached in AlgTopCached14.\<close>

\<comment> \<open>Helper: quotient\\_of\\_scheme\\_on implies length \\<ge> 3 (from polygonal region).\<close>
lemma quotient_scheme_length_ge3:
  "top1_quotient_of_scheme_on Y TY w \<Longrightarrow> length w \<ge> 3"
proof -
  assume "top1_quotient_of_scheme_on Y TY w"
  then obtain P q vx vy where "top1_is_polygonal_region_on P (length w)"
    by (rule quotient_of_scheme_extract_vx)
  thus "length w \<ge> 3" unfolding top1_is_polygonal_region_on_def by (by100 blast)
qed

\<comment> \<open>Edge-interior point is never a vertex (for any polygon with C3 + C11).
   Proof: collinearity implies cross product = 0, but C11 forces < 0 for non-adjacent vertices.
   Adjacent vertex case: would give (vx i, vy i) = (vx(i+1), vy(i+1)), contradicting C3.\<close>
lemma edge_interior_not_vertex:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat
  assumes hn: "n \<ge> 3"
      and hC3: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
      and hC11: "\<forall>i<n. \<forall>k<n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod n \<longrightarrow>
          (vx k - vx i) * (vy(Suc i mod n) - vy i) - (vy k - vy i) * (vx(Suc i mod n) - vx i) < 0"
      and hidx: "idx < n" and ht0: "0 < t" and ht1: "t < 1"
  shows "\<not>(\<exists>k<n. (1-t)*vx idx + t*vx(Suc idx mod n) = vx k
                \<and> (1-t)*vy idx + t*vy(Suc idx mod n) = vy k)"
proof
  assume "\<exists>k<n. (1-t)*vx idx + t*vx(Suc idx mod n) = vx k
              \<and> (1-t)*vy idx + t*vy(Suc idx mod n) = vy k"
  then obtain k where hk: "k < n"
    and hxeq: "(1-t)*vx idx + t*vx(Suc idx mod n) = vx k"
    and hyeq: "(1-t)*vy idx + t*vy(Suc idx mod n) = vy k" by (by100 blast)
  \<comment> \<open>Collinearity: (vx k - vx idx, vy k - vy idx) = t * (vx(Suc idx mod n) - vx idx, ...).\<close>
  have hcolx: "vx k - vx idx = t * (vx(Suc idx mod n) - vx idx)"
  proof -
    from hxeq have "vx k - vx idx = t*vx(Suc idx mod n) - t*vx idx" by argo
    thus ?thesis by (simp only: right_diff_distrib[symmetric])
  qed
  have hcoly: "vy k - vy idx = t * (vy(Suc idx mod n) - vy idx)"
  proof -
    from hyeq have "vy k - vy idx = t*vy(Suc idx mod n) - t*vy idx" by argo
    thus ?thesis by (simp only: right_diff_distrib[symmetric])
  qed
  \<comment> \<open>Cross product = 0 (collinear with edge direction).\<close>
  have hcross0: "(vx k - vx idx)*(vy(Suc idx mod n) - vy idx)
      - (vy k - vy idx)*(vx(Suc idx mod n) - vx idx) = 0"
    unfolding hcolx hcoly by (by100 algebra)
  \<comment> \<open>By C11: k must be idx or Suc idx mod n (other vertices have cross product < 0).\<close>
  have "k = idx \<or> k = Suc idx mod n"
  proof (rule ccontr)
    assume "\<not>(k = idx \<or> k = Suc idx mod n)"
    hence "k \<noteq> idx" "k \<noteq> Suc idx mod n" by (by100 auto)+
    from hC11[rule_format, OF hidx hk this]
    have "(vx k - vx idx)*(vy(Suc idx mod n) - vy idx)
        - (vy k - vy idx)*(vx(Suc idx mod n) - vx idx) < 0" .
    thus False using hcross0 by (by100 linarith)
  qed
  thus False
  proof
    assume "k = idx"
    hence "vx k = vx idx" "vy k = vy idx" by (by100 auto)+
    hence "t * (vx(Suc idx mod n) - vx idx) = 0" using hcolx by (by100 linarith)
    hence "vx(Suc idx mod n) = vx idx" using ht0 by (by100 simp)
    moreover have "t * (vy(Suc idx mod n) - vy idx) = 0" using hcoly \<open>vy k = vy idx\<close> by (by100 linarith)
    hence "vy(Suc idx mod n) = vy idx" using ht0 by (by100 simp)
    ultimately have "(vx idx, vy idx) = (vx(Suc idx mod n), vy(Suc idx mod n))" by (by100 simp)
    have "Suc idx mod n < n" using hn by (by100 simp)
    have hmod_lt: "Suc idx mod n < n" using hn by (by100 simp)
    have hmod_ne: "idx \<noteq> Suc idx mod n"
    proof (cases "idx < n - 1")
      case True hence "Suc idx < n" by (by100 linarith)
      hence "Suc idx mod n = Suc idx" by (by100 simp)
      thus ?thesis by (by100 simp)
    next
      case False hence "idx = n - 1" using hidx by (by100 linarith)
      hence "Suc idx = n" using hn by (by100 linarith)
      hence "Suc idx mod n = 0" using hn by (by100 simp)
      thus ?thesis using \<open>idx = n - 1\<close> hn by (by100 linarith)
    qed
    from hC3[rule_format, OF hidx hmod_lt hmod_ne]
    show False using \<open>(vx idx, vy idx) = _\<close> by (by100 blast)
  next
    assume "k = Suc idx mod n"
    hence "vx k = vx(Suc idx mod n)" "vy k = vy(Suc idx mod n)" by (by100 auto)+
    hence "vx(Suc idx mod n) - vx idx = t * (vx(Suc idx mod n) - vx idx)" using hcolx by (by100 linarith)
    hence "(1-t) * (vx(Suc idx mod n) - vx idx) = 0" by argo
    hence "vx(Suc idx mod n) = vx idx" using ht1 by (by100 simp)
    moreover have "(1-t) * (vy(Suc idx mod n) - vy idx) = 0"
    proof -
      from \<open>vy k = vy(Suc idx mod n)\<close> hcoly
      have "vy(Suc idx mod n) - vy idx = t * (vy(Suc idx mod n) - vy idx)" by (by100 linarith)
      thus ?thesis by argo
    qed
    hence "vy(Suc idx mod n) = vy idx" using ht1 by (by100 simp)
    ultimately have "(vx idx, vy idx) = (vx(Suc idx mod n), vy(Suc idx mod n))" by (by100 simp)
    have hmod_lt2: "Suc idx mod n < n" using hn by (by100 simp)
    have hmod_ne2: "idx \<noteq> Suc idx mod n"
    proof (cases "idx < n - 1")
      case True hence "Suc idx < n" by (by100 linarith)
      hence "Suc idx mod n = Suc idx" by (by100 simp)
      thus ?thesis by (by100 simp)
    next
      case False hence "idx = n - 1" using hidx by (by100 linarith)
      hence "Suc idx = n" using hn by (by100 linarith)
      hence "Suc idx mod n = 0" using hn by (by100 simp)
      thus ?thesis using \<open>idx = n - 1\<close> hn by (by100 linarith)
    qed
    from hC3[rule_format, OF hidx \<open>Suc idx mod n < n\<close> this]
    show False using \<open>(vx idx, vy idx) = _\<close> by (by100 blast)
  qed
qed

\<comment> \<open>AM-GM for real products: |xy| \\<le> (x^2+y^2)/2. Reusable for inner product bounds (expert audit 26).\<close>
lemma real_abs_mul_le_half_sum_squares:
  fixes x y :: real
  shows "abs (x * y) \<le> (x^2 + y^2) / 2"
proof -
  have h0: "0 \<le> (abs x - abs y)^2" by simp
  have h1: "(abs x - abs y)^2 = x^2 + y^2 - 2 * abs (x * y)"
    by (simp add: power2_eq_square abs_mult algebra_simps)
  from h0 h1 have h2: "2 * abs (x * y) \<le> x^2 + y^2" by linarith
  show ?thesis using h2 by simp
qed

\<comment> \<open>Two-coordinate inner-product bound (expert audit 26 §2).\<close>
lemma real_inner2_abs_le_half_norm_sums:
  fixes sx sy dx dy S D :: real
  assumes hs: "sx^2 + sy^2 \<le> S"
      and hd: "dx^2 + dy^2 \<le> D"
  shows "abs (sx * dx + sy * dy) \<le> (S + D) / 2"
proof -
  have htri: "abs (sx * dx + sy * dy) \<le> abs (sx * dx) + abs (sy * dy)"
    by (rule abs_triangle_ineq)
  have hx: "abs (sx * dx) \<le> (sx^2 + dx^2) / 2"
    by (rule real_abs_mul_le_half_sum_squares)
  have hy: "abs (sy * dy) \<le> (sy^2 + dy^2) / 2"
    by (rule real_abs_mul_le_half_sum_squares)
  have "abs (sx * dx) + abs (sy * dy)
        \<le> ((sx^2 + sy^2) + (dx^2 + dy^2)) / 2"
    using hx hy by simp
  also have "\<dots> \<le> (S + D) / 2"
    using hs hd by simp
  finally show ?thesis using htri by linarith
qed

\<comment> \<open>Polar decomposition: x = r*cos(\\<theta>), y = r*sin(\\<theta>) where r = sqrt(x^2+y^2)
   and \\<theta> = arccos(x/r) or 2\\<pi>-arccos(x/r) depending on sign of y.\<close>
lemma polar_decomposition_fst:
  fixes x y :: real
  assumes hpos: "x^2 + y^2 > 0"
  shows "sqrt (x^2 + y^2) * cos (if y \<ge> 0 then arccos (x / sqrt (x^2 + y^2))
         else 2*pi - arccos (x / sqrt (x^2 + y^2))) = x"
proof -
  define r where "r = sqrt (x^2 + y^2)"
  have hr_pos: "r > 0" unfolding r_def using hpos
    using real_sqrt_gt_0_iff by (by100 auto)
  have hr_sq: "r^2 = x^2 + y^2" unfolding r_def
    using real_sqrt_pow2[OF less_imp_le[OF hpos]] by (by100 blast)
  have hxr_le: "x^2 \<le> r^2"
  proof -
    have "y^2 \<ge> 0" by (by100 simp)
    thus ?thesis using hr_sq by (by100 linarith)
  qed
  have hfp: "x \<le> r" using power2_le_imp_le[OF hxr_le] hr_pos by (by100 linarith)
  have "(-x)^2 \<le> r^2"
  proof -
    have "(-x)^2 = x^2" unfolding power2_eq_square by (by100 simp)
    thus ?thesis using hxr_le by (by100 linarith)
  qed
  hence hmx: "-x \<le> r"
    using power2_le_imp_le[OF _ less_imp_le[OF hr_pos]] by (by100 blast)
  from divide_right_mono[OF hmx, of r] hr_pos
  have h_lb: "-1 \<le> x / r" by (by100 simp)
  from divide_right_mono[OF hfp, of r] hr_pos
  have h_ub: "x / r \<le> 1" by (by100 simp)
  have hcos: "cos (arccos (x / r)) = x / r"
    using cos_arccos[OF h_lb h_ub] .
  hence h1: "r * cos (arccos (x / r)) = x" using hr_pos by (by100 simp)
  have hcos2: "cos (2*pi - arccos (x / r)) = cos (arccos (x / r))"
    by (simp add: cos_diff)
  hence h2: "r * cos (2*pi - arccos (x / r)) = x" using h1 by (by100 simp)
  show ?thesis unfolding r_def[symmetric] using h1 h2 by (by100 simp)
qed

lemma polar_decomposition_snd:
  fixes x y :: real
  assumes hpos: "x^2 + y^2 > 0"
  shows "sqrt (x^2 + y^2) * sin (if y \<ge> 0 then arccos (x / sqrt (x^2 + y^2))
         else 2*pi - arccos (x / sqrt (x^2 + y^2))) = y"
proof -
  define r where "r = sqrt (x^2 + y^2)"
  have hr_pos: "r > 0" unfolding r_def using hpos
    using real_sqrt_gt_0_iff by (by100 auto)
  have hr_sq: "r^2 = x^2 + y^2" unfolding r_def
    using real_sqrt_pow2[OF less_imp_le[OF hpos]] by (by100 blast)
  \<comment> \<open>Arccos preconditions.\<close>
  have hxr_le: "x^2 \<le> r^2"
  proof -
    have "y^2 \<ge> 0" by (by100 simp)
    thus ?thesis using hr_sq by (by100 linarith)
  qed
  have hfp: "x \<le> r" using power2_le_imp_le[OF hxr_le] hr_pos by (by100 linarith)
  have "(-x)^2 \<le> r^2"
  proof -
    have "(-x)^2 = x^2" unfolding power2_eq_square by (by100 simp)
    thus ?thesis using hxr_le by (by100 linarith)
  qed
  hence hmx: "-x \<le> r" using power2_le_imp_le[OF _ less_imp_le[OF hr_pos]] by (by100 blast)
  from divide_right_mono[OF hmx, of r] hr_pos have h_lb: "-1 \<le> x / r" by (by100 simp)
  from divide_right_mono[OF hfp, of r] hr_pos have h_ub: "x / r \<le> 1" by (by100 simp)
  \<comment> \<open>sin(arccos(x/r)) = sqrt(1-(x/r)^2). And r*sqrt(1-(x/r)^2) = sqrt(r^2-x^2) = sqrt(y^2) = |y|.\<close>
  have hsin_val: "sin (arccos (x / r)) = sqrt (1 - (x/r)^2)"
    using sin_arccos[OF h_lb h_ub] .
  have hxr_sq_le: "(x/r)^2 \<le> 1"
  proof -
    have "x/r \<le> 1" using h_ub .
    moreover have "-(x/r) \<le> 1" using h_lb by (by100 linarith)
    ultimately have "abs (x/r) \<le> 1" by (by100 linarith)
    hence hle: "x/r \<le> 1" and hge: "-1 \<le> x/r" by (by100 linarith)+
    show ?thesis unfolding power2_eq_square
    proof (cases "x/r \<ge> 0")
      case True
      have "x/r * (x/r) \<le> 1 * 1"
      proof (rule mult_mono)
        show "x/r \<le> 1" using hle .
        show "x/r \<le> 1" using hle .
        show "(0::real) \<le> 1" by (by100 simp)
        show "0 \<le> x/r" using True .
      qed
      thus "x / r * (x / r) \<le> 1" by (by100 simp)
    next
      case False
      hence hn: "x/r < 0" by (by100 linarith)
      have "-(x/r) \<le> 1" using hge by (by100 linarith)
      have "(-x/r) * (-x/r) \<le> 1 * 1"
      proof (rule mult_mono)
        show "-x/r \<le> 1" using \<open>-(x/r) \<le> 1\<close> by (by100 simp)
        show "-x/r \<le> 1" using \<open>-(x/r) \<le> 1\<close> by (by100 simp)
        show "(0::real) \<le> 1" by (by100 simp)
        show "0 \<le> -x/r" using hn by (by100 linarith)
      qed
      thus "x / r * (x / r) \<le> 1" by (by100 simp)
    qed
  qed
  have hsin_nn: "sin (arccos (x / r)) \<ge> 0"
    using hsin_val hxr_sq_le by (by100 simp)
  have h_r_sin: "r * sin (arccos (x / r)) = abs y"
  proof -
    have "r * sqrt (1 - (x/r)^2) = sqrt (r^2 * (1 - (x/r)^2))"
      using hr_pos by (simp add: real_sqrt_mult)
    also have "r^2 * (1 - (x/r)^2) = r^2 - x^2"
    proof -
      have "r * r \<noteq> 0" using hr_pos by (by100 simp)
      hence "r * r * (1 - x * x / (r * r)) = r * r - x * x"
        by (simp add: field_simps)
      thus ?thesis unfolding power2_eq_square using hr_pos by (simp add: field_simps)
    qed
    also have "\<dots> = y^2" using hr_sq by (by100 linarith)
    also have "sqrt (y^2) = abs y" by (rule real_sqrt_abs)
    finally show ?thesis using hsin_val by (by100 simp)
  qed
  \<comment> \<open>Case split on y \\<ge> 0.\<close>
  show ?thesis
  proof (cases "y \<ge> 0")
    case True
    have "r * sin (arccos (x / r)) = y" using h_r_sin True by (by100 simp)
    thus ?thesis unfolding r_def[symmetric] using True by (by100 simp)
  next
    case False
    have "sin (2*pi - arccos (x / r)) = - sin (arccos (x / r))"
      by (simp add: sin_diff)
    hence "r * sin (2*pi - arccos (x / r)) = -(r * sin (arccos (x / r)))"
      by (by100 simp)
    also have "\<dots> = - abs y" using h_r_sin by (by100 simp)
    also have "\<dots> = y" using False by (by100 simp)
    finally have "r * sin (2*pi - arccos (x / r)) = y" .
    thus ?thesis unfolding r_def[symmetric] using False by (by100 simp)
  qed
qed

\<comment> \<open>Angle recovery: the angle computed from (r*cos \\<alpha>, r*sin \\<alpha>) via arccos recovers \\<alpha> for \\<alpha> \\<in> [0,2\\<pi>).\<close>
lemma angle_recovery:
  fixes r \<alpha> :: real
  assumes hr: "r > 0" and h\<alpha>0: "0 \<le> \<alpha>" and h\<alpha>2: "\<alpha> < 2*pi"
  shows "(if r * sin \<alpha> \<ge> 0 then arccos ((r * cos \<alpha>) / sqrt ((r*cos \<alpha>)^2 + (r*sin \<alpha>)^2))
         else 2*pi - arccos ((r * cos \<alpha>) / sqrt ((r*cos \<alpha>)^2 + (r*sin \<alpha>)^2))) = \<alpha>"
proof -
  \<comment> \<open>Step 1: sqrt((r*cos)^2 + (r*sin)^2) = r.\<close>
  have "(r * cos \<alpha>)^2 + (r * sin \<alpha>)^2 = r^2 * (cos \<alpha> ^2 + sin \<alpha> ^2)"
    unfolding power2_eq_square by argo
  also have "\<dots> = r^2" using sin_cos_squared_add3 by (by100 simp)
  finally have hsqrt: "sqrt ((r*cos \<alpha>)^2 + (r*sin \<alpha>)^2) = r"
    using hr by (by100 simp)
  \<comment> \<open>Step 2: (r*cos \\<alpha>)/r = cos \\<alpha>.\<close>
  have hdiv: "(r * cos \<alpha>) / sqrt ((r*cos \<alpha>)^2 + (r*sin \<alpha>)^2) = cos \<alpha>"
    using hsqrt hr by (by100 simp)
  \<comment> \<open>Step 3: arccos(cos \\<alpha>) = \\<alpha> for \\<alpha> \\<in> [0,\\<pi>], arccos(cos \\<alpha>) = 2\\<pi>-\\<alpha> for \\<alpha> \\<in> (\\<pi>,2\\<pi>).\<close>
  show ?thesis unfolding hdiv
  proof (cases "\<alpha> \<le> pi")
    case True
    \<comment> \<open>\\<alpha> \\<in> [0,\\<pi>]: arccos(cos \\<alpha>) = \\<alpha>, and sin \\<alpha> \\<ge> 0.\<close>
    have "arccos (cos \<alpha>) = \<alpha>" using arccos_cos[OF h\<alpha>0 True] .
    moreover have "r * sin \<alpha> \<ge> 0"
      using hr sin_ge_zero[OF h\<alpha>0 True] by (by100 simp)
    ultimately show "(if r * sin \<alpha> \<ge> 0 then arccos (cos \<alpha>) else 2*pi - arccos (cos \<alpha>)) = \<alpha>"
      by (by100 simp)
  next
    case False
    hence h\<alpha>_gt_pi: "\<alpha> > pi" by (by100 linarith)
    \<comment> \<open>\\<alpha> \\<in> (\\<pi>, 2\\<pi>): cos \\<alpha> = cos(2\\<pi>-\\<alpha>) and 2\\<pi>-\\<alpha> \\<in> (0, \\<pi>).\<close>
    have h2pa: "2*pi - \<alpha> > 0" using h\<alpha>2 by (by100 linarith)
    have h2pa_pi: "2*pi - \<alpha> < pi" using h\<alpha>_gt_pi by (by100 linarith)
    have hcos_eq: "cos \<alpha> = cos (2*pi - \<alpha>)" by (simp add: cos_diff)
    have harccos: "arccos (cos \<alpha>) = 2*pi - \<alpha>"
    proof -
      from arccos_cos[OF less_imp_le[OF h2pa] less_imp_le[OF h2pa_pi]]
      have "arccos (cos (2*pi - \<alpha>)) = 2*pi - \<alpha>" .
      thus ?thesis unfolding hcos_eq[symmetric] .
    qed
    have "2*pi - arccos (cos \<alpha>) = \<alpha>" using harccos by (by100 linarith)
    moreover have "\<not> (r * sin \<alpha> \<ge> 0)"
    proof -
      have "sin \<alpha> < 0" using sin_lt_zero[OF h\<alpha>_gt_pi h\<alpha>2] .
      hence "r * sin \<alpha> < 0"
        using mult_pos_neg[OF hr] by (by100 blast)
      thus ?thesis by (by100 linarith)
    qed
    ultimately show "(if r * sin \<alpha> \<ge> 0 then arccos (cos \<alpha>) else 2*pi - arccos (cos \<alpha>)) = \<alpha>"
      by (by100 simp)
  qed
qed

\<comment> \<open>Arccos precondition: -1 \\<le> x / sqrt(x^2+y^2) \\<le> 1 for (x,y) \\<noteq> (0,0). Reusable helper.\<close>
lemma fst_div_norm_bounded:
  fixes x y :: real
  assumes "x \<noteq> 0 \<or> y \<noteq> 0"
  shows "-1 \<le> x / sqrt (x^2 + y^2)" and "x / sqrt (x^2 + y^2) \<le> 1"
proof -
  have hpos: "x^2 + y^2 > 0" using assms
  proof
    assume "x \<noteq> 0" hence "x^2 > 0" by (by100 simp)
    moreover have "y^2 \<ge> 0" by (by100 simp)
    ultimately show ?thesis by (by100 linarith)
  next
    assume "y \<noteq> 0" hence "y^2 > 0" by (by100 simp)
    moreover have "x^2 \<ge> 0" by (by100 simp)
    ultimately show ?thesis by (by100 linarith)
  qed
  have hr: "sqrt (x^2 + y^2) > 0" using hpos real_sqrt_gt_0_iff by (by100 auto)
  have hsq: "(sqrt (x^2 + y^2))^2 = x^2 + y^2"
    using real_sqrt_pow2[OF less_imp_le[OF hpos]] by (by100 blast)
  have hx_le: "x^2 \<le> (sqrt (x^2 + y^2))^2"
  proof - have "y^2 \<ge> 0" by (by100 simp) thus ?thesis using hsq by (by100 linarith) qed
  have hx_pos: "x \<le> sqrt (x^2 + y^2)"
    using power2_le_imp_le[OF hx_le] hr by (by100 linarith)
  have "(-x)^2 \<le> (sqrt (x^2+y^2))^2"
    using hx_le unfolding power2_eq_square by (by100 linarith)
  hence hmx_pos: "-x \<le> sqrt (x^2+y^2)"
    using power2_le_imp_le[OF _ less_imp_le[OF hr]] by (by100 blast)
  show "-1 \<le> x / sqrt (x^2 + y^2)"
  proof -
    from hmx_pos have "- 1 * sqrt (x^2+y^2) \<le> x" by (by100 linarith)
    with hr show ?thesis by (simp add: pos_le_divide_eq)
  qed
  show "x / sqrt (x^2 + y^2) \<le> 1"
  proof -
    from hx_pos have "x \<le> 1 * sqrt (x^2+y^2)" by (by100 linarith)
    with hr show ?thesis by (simp add: pos_divide_le_eq)
  qed
qed

\<comment> \<open>Cancel shift: edge i+2 in [a,a\\<inverse>]@w has same label/direction as edge i in w (expert audit 26 §7).\<close>
lemma cancel_shift_label:
  fixes a :: "'a \<times> bool" and w :: "('a \<times> bool) list" and i :: nat
  assumes "i < length w"
  shows "([a, top1_inverse_edge a] @ w) ! (i + 2) = w ! i"
  by (by100 simp)

\<comment> \<open>Cancel shift preserves label matching: partner edges shift by 2.\<close>
lemma cancel_shift_partner:
  fixes a :: "'a \<times> bool" and w :: "('a \<times> bool) list" and i j :: nat
  assumes "i < length w" "j < length w"
  shows "fst (([a, top1_inverse_edge a] @ w) ! (i + 2)) = fst (([a, top1_inverse_edge a] @ w) ! (j + 2))
     \<longleftrightarrow> fst (w ! i) = fst (w ! j)"
    and "snd (([a, top1_inverse_edge a] @ w) ! (i + 2)) = snd (([a, top1_inverse_edge a] @ w) ! (j + 2))
     \<longleftrightarrow> snd (w ! i) = snd (w ! j)"
  using cancel_shift_label[OF assms(1), of a] cancel_shift_label[OF assms(2), of a]
  by (by100 simp)+

\<comment> \<open>Identity homeomorphism + same-space helper (moved here for use by cut-paste lemmas).\<close>
lemma homeomorphism_id_early:
  assumes "is_topology_on X TX"
  shows "top1_homeomorphism_on X TX X TX id"
proof -
  have hid_cont: "top1_continuous_map_on X TX X TX id"
    by (rule top1_continuous_map_on_id[OF assms])
  have hinv: "\<forall>x\<in>X. inv_into X id x = x"
  proof
    fix x assume "x \<in> X"
    thus "inv_into X id x = x" using inv_into_f_f[OF inj_on_id \<open>x \<in> X\<close>] by simp
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

lemma same_space_implies_homeo_realization_early:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_quotient_of_scheme_on X TX t"
  shows "\<exists>(Y :: 'a set) (TY :: 'a set set) (h :: 'a \<Rightarrow> 'a).
    top1_quotient_of_scheme_on Y TY t \<and>
    top1_homeomorphism_on X TX Y TY h"
proof -
  have "is_topology_on X TX"
    using assms unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
  show ?thesis
    using assms homeomorphism_id_early[OF \<open>is_topology_on X TX\<close>] by (by100 blast)
qed

\<comment> \<open>Regular n-gon is a polygonal region. Standalone helper for reuse.\<close>

\<comment> \<open>regular\\_ngon\\_polygonal\\_region and quotient\\_scheme\\_edge\\_permutation DELETED
   per expert audit 24: both unused (edge\\_permutation never referenced by cut-paste,
   and regular\\_ngon only referenced by edge\\_permutation).
   The classification uses a different route via scheme\\_quotient\\_exists + uniqueness.\<close>


\<comment> \<open>Cut-paste preservation: homeomorphic realization (per audit 22 §5.5).
   The quotient of the cut-paste rearranged scheme is homeomorphic to the original.
   Book: Munkres §76, Theorem 76.1. Cut along diagonal, rearrange, paste.
   Uses quotient\\_scheme\\_same\\_labels\\_rearrange for the same-space construction.\<close>
\<comment> \<open>Cut-paste §76(iv): homeomorphic realization via polygon\\_cut\\_reglue (Munkres Theorem 76.1).
   Per audit 22 §5.5: one geometric theorem for all three cut-paste variants.\<close>
lemma scheme_quotient_exists:
  fixes scheme :: "(nat \<times> bool) list"
  assumes "length scheme \<ge> 3"
      and hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
  shows "\<exists>(Y :: (real \<times> real) set) (TY :: (real \<times> real) set set).
    top1_quotient_of_scheme_on Y TY scheme" (is ?C1)
  and "\<exists>(P :: (real \<times> real) set) q (vx :: nat \<Rightarrow> real) (vy :: nat \<Rightarrow> real)
    (Y :: (real \<times> real) set) (TY :: (real \<times> real) set set).
    top1_quotient_of_scheme_on Y TY scheme
    \<and> top1_is_polygonal_region_on P (length scheme)
    \<and> top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q
    \<and> (\<forall>i<length scheme. \<forall>j<length scheme. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
    \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
    \<and> P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                   \<and> (\<Sum>i<length scheme. coeffs i) = 1
                   \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                   \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}
    \<and> (\<forall>i<length scheme. \<forall>j<length scheme. fst(scheme!i)=fst(scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t)*vx i+t*vx(Suc i mod length scheme),(1-t)*vy i+t*vy(Suc i mod length scheme))
         = (if snd(scheme!i)=snd(scheme!j)
            then q ((1-t)*vx j+t*vx(Suc j mod length scheme),(1-t)*vy j+t*vy(Suc j mod length scheme))
            else q (t*vx j+(1-t)*vx(Suc j mod length scheme),t*vy j+(1-t)*vy(Suc j mod length scheme)))))
    \<and> (\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t)*vx i+t*vx(Suc i mod length scheme),(1-t)*vy i+t*vy(Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p'))
    \<and> (\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
        q ((1-t)*vx i+t*vx(Suc i mod length scheme),(1-t)*vy i+t*vy(Suc i mod length scheme))
      = q ((1-s)*vx j+s*vx(Suc j mod length scheme),(1-s)*vy j+s*vy(Suc j mod length scheme))
      \<longrightarrow> (i=j \<and> t=s) \<or> (fst(scheme!i)=fst(scheme!j) \<and> (if snd(scheme!i)=snd(scheme!j) then s=t else s=1-t)))
    \<and> (\<forall>i<length scheme. let cx=(\<Sum>j<length scheme. vx j)/real(length scheme);
                             cy=(\<Sum>j<length scheme. vy j)/real(length scheme)
         in (vx i-cx)*(vy(Suc i mod length scheme)-cy)-(vy i-cy)*(vx(Suc i mod length scheme)-cx) > 0)
    \<and> (\<forall>i<length scheme. \<forall>k<length scheme. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod length scheme \<longrightarrow>
        (vx k-vx i)*(vy(Suc i mod length scheme)-vy i)-(vy k-vy i)*(vx(Suc i mod length scheme)-vx i) < 0)
    \<and> (\<forall>k<length scheme. \<forall>j<length scheme. \<forall>s\<in>{0<..<(1::real)}.
        q (vx k, vy k) \<noteq> q ((1-s)*vx j + s*vx(Suc j mod length scheme),
                               (1-s)*vy j + s*vy(Suc j mod length scheme)))
    \<and> (\<exists>vtgt. (\<forall>k<length scheme. q (vx k, vy k) = (vx (vtgt k), vy (vtgt k)))
             \<and> (\<forall>k<length scheme. vtgt k < length scheme)
             \<and> (\<forall>k<length scheme. vtgt k \<le> k)
             \<and> (\<forall>k<length scheme. vtgt (vtgt k) = vtgt k)
             \<and> (\<forall>k<length scheme. \<forall>l<length scheme. vtgt k = vtgt l \<longrightarrow>
                (k, l) \<in> {(a, b). \<exists>i<length scheme. \<exists>j<length scheme. i \<noteq> j
                  \<and> fst (scheme ! i) = fst (scheme ! j)
                  \<and> ((snd (scheme ! i) = snd (scheme ! j) \<and> a = i \<and> b = j)
                   \<or> (snd (scheme ! i) = snd (scheme ! j) \<and> a = Suc i mod length scheme \<and> b = Suc j mod length scheme)
                   \<or> (snd (scheme ! i) \<noteq> snd (scheme ! j) \<and> a = i \<and> b = Suc j mod length scheme)
                   \<or> (snd (scheme ! i) \<noteq> snd (scheme ! j) \<and> a = Suc i mod length scheme \<and> b = j))}\<^sup>*))" (is ?C2)
proof -
  let ?n = "length scheme"
  \<comment> \<open>Regular n-gon: vertices at (cos(2\\<pi>k/n), sin(2\\<pi>k/n)).\<close>
  define vx where "vx k = cos (2 * pi * real k / real ?n)" for k
  define vy where "vy k = sin (2 * pi * real k / real ?n)" for k
  \<comment> \<open>P = convex hull of vertices.\<close>
  define P where "P = {(x::real,y::real). \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                     \<and> (\<Sum>i<?n. coeffs i) = 1
                     \<and> x = (\<Sum>i<?n. coeffs i * vx i)
                     \<and> y = (\<Sum>i<?n. coeffs i * vy i)}"
  \<comment> \<open>Quotient map: on boundary, identify edges per scheme. Interior maps injectively.
     For edge i (from v\\_i to v\\_{i+1}), at parameter t \\<in> [0,1]:
       point = ((1-t)*vx i + t*vx(Suc i mod n), (1-t)*vy i + t*vy(Suc i mod n))
     If edge i is identified with edge j (same label):
       - same direction: q(edge\\_i(t)) = q(edge\\_j(t))
       - opposite direction: q(edge\\_i(t)) = q(edge\\_j(1-t))
     For interior points (not on any edge): q = id (no identification).\<close>
  \<comment> \<open>Define q via representatives: for each boundary point, pick canonical edge/param.\<close>
  \<comment> \<open>Edge point helper: point on edge i at parameter t.\<close>
  define edge_pt where "edge_pt i t = ((1-t)*vx i + t*vx(Suc i mod ?n),
                                        (1-t)*vy i + t*vy(Suc i mod ?n))" for i t
  \<comment> \<open>For each edge position i, find the partner position (same label, other occurrence).
     For a proper scheme, each label appears 0 or 2 times.\<close>
  define partner where "partner i = (SOME j. j < ?n \<and> j \<noteq> i \<and> fst(scheme!i) = fst(scheme!j))" for i
  \<comment> \<open>Is edge i the canonical one (lower index) of its pair?\<close>
  define is_canonical where "is_canonical i = (i \<le> partner i)" for i
  \<comment> \<open>Partner properties (from properness of scheme).\<close>
  have partner_props: "\<And>i. i < ?n \<Longrightarrow> card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} = 2 \<Longrightarrow>
      partner i < ?n \<and> partner i \<noteq> i \<and> fst(scheme!(partner i)) = fst(scheme!i)"
  proof -
    fix i assume hi: "i < ?n" and hcard: "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} = 2"
    \<comment> \<open>The set has exactly 2 elements, one of which is i. The other is partner(i).\<close>
    have "i \<in> {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)}" using hi by (by100 simp)
    hence "\<exists>j. j \<in> {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} \<and> j \<noteq> i"
    proof -
      have "card ({j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} - {i}) = 1"
        using hcard \<open>i \<in> _\<close> by (by100 simp)
      hence "{j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} - {i} \<noteq> {}" by (by100 force)
      thus ?thesis by (by100 blast)
    qed
    then obtain j where hj: "j < ?n" "j \<noteq> i" "fst(scheme!j) = fst(scheme!i)" by (by100 blast)
    have hex: "\<exists>j. j < ?n \<and> j \<noteq> i \<and> fst(scheme!i) = fst(scheme!j)"
      using hj(1) hj(2) hj(3)[symmetric] by (by100 blast)
    have "partner i < ?n \<and> partner i \<noteq> i \<and> fst(scheme!i) = fst(scheme!(partner i))"
      unfolding partner_def using someI_ex[OF hex] by (by100 blast)
    thus "partner i < ?n \<and> partner i \<noteq> i \<and> fst(scheme!(partner i)) = fst(scheme!i)"
      by (by100 simp)
  qed
  \<comment> \<open>Partner uniqueness: for proper scheme, partner is the unique other edge with same label.\<close>
  have partner_unique: "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow> i \<noteq> j \<Longrightarrow> fst(scheme!i) = fst(scheme!j) \<Longrightarrow>
      partner i = j"
  proof -
    fix i j assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j" and hlabel: "fst(scheme!i) = fst(scheme!j)"
    \<comment> \<open>The set {k. k < n \\<and> fst(scheme!k) = fst(scheme!i)} has exactly 2 elements: i and j.\<close>
    have hcard: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = 2"
    proof -
      have "i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hi by (by100 simp)
      have hfin: "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" by (by100 simp)
      have hne: "{k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<noteq> {}" using \<open>i \<in> _\<close> by (by100 blast)
      have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<noteq> 0" using hfin hne by (by100 simp)
      hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<ge> 1" by (by100 linarith)
      moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<in> {0, 2}"
        using hproper by (by100 blast)
      ultimately show ?thesis
      proof (cases "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = 0")
        case True thus ?thesis using \<open>_ \<ge> 1\<close> by (by100 linarith)
      next
        case False thus ?thesis using \<open>_ \<in> {0,2}\<close> by (by100 blast)
      qed
    qed
    \<comment> \<open>The set is exactly {i, j}.\<close>
    have hset: "{k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = {i, j}"
    proof -
      have "i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hi by (by100 simp)
      have "j \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hj hlabel by (by100 simp)
      have "card {i, j} = 2" using hij by (by100 simp)
      have "{i, j} \<subseteq> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}"
        using \<open>i \<in> _\<close> \<open>j \<in> _\<close> by (by100 blast)
      have hfin: "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" by (by100 simp)
      from card_subset_eq[OF hfin \<open>{i,j} \<subseteq> _\<close>]
      show ?thesis using hcard \<open>card {i,j} = 2\<close> by (by100 simp)
    qed
    \<comment> \<open>partner(i) is the unique k \\<noteq> i with same label. Since the set is {i,j}, partner(i) = j.\<close>
    have "partner i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<and> partner i \<noteq> i"
      using partner_props[OF hi hcard] hlabel by (by100 blast)
    hence "partner i \<in> {i, j} \<and> partner i \<noteq> i" using hset by (by100 blast)
    thus "partner i = j" by (by100 blast)
  qed
  \<comment> \<open>Vertex equivalence: one-step identification pairs from all edge pairings.\<close>
  define vtx_id :: "(nat \<times> nat) set" where "vtx_id =
    (\<Union>idx \<in> {..<?n}. let j = partner idx in
      if snd(scheme!idx) = snd(scheme!j) then {(idx, j), (Suc idx mod ?n, Suc j mod ?n)}
      else {(idx, Suc j mod ?n), (Suc idx mod ?n, j)})"
  \<comment> \<open>Vertex target: LEAST vertex reachable via symmetric closure of vtx\\_id.
     This correctly computes the equivalence class representative even when
     vertex identifications chain across multiple edge pairings.\<close>
  define vtgt where "vtgt k = (LEAST m. (k, m) \<in> (vtx_id \<union> (converse vtx_id) \<union> Id)\<^sup>*)" for k
  \<comment> \<open>Key property: vertices in the same equivalence class have the same vtgt representative.\<close>
  have vtgt_class: "\<And>k1 k2. (k1, k2) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>* \<Longrightarrow> vtgt k1 = vtgt k2"
  proof -
    fix k1 k2 :: nat assume hrel: "(k1, k2) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
    have hsym: "sym (vtx_id \<union> converse vtx_id \<union> Id)" unfolding sym_def by (by100 blast)
    from sym_rtrancl[OF hsym] have hsymR: "sym ((vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*)" .
    hence hrev: "(k2, k1) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
      using hrel unfolding sym_def by (by100 blast)
    have "{m. (k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*}
        = {m. (k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*}"
    proof (intro equalityI subsetI CollectI)
      fix m assume "m \<in> {m. (k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*}"
      hence "(k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 simp)
      with hrev show "(k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
        by (rule rtrancl_trans)
    next
      fix m assume "m \<in> {m. (k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*}"
      hence "(k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 simp)
      with hrel show "(k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
        by (rule rtrancl_trans)
    qed
    hence "(\<lambda>m. (k1, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*)
         = (\<lambda>m. (k2, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*)"
      by (by100 auto)
    thus "vtgt k1 = vtgt k2" unfolding vtgt_def by (by100 simp)
  qed
  \<comment> \<open>Quotient map q (3-branch): vertex \\<to> vtgt, edge interior \\<to> partner, else \\<to> identity.\<close>
  define q :: "(real \<times> real) \<Rightarrow> (real \<times> real)" where
    "q p = (if \<exists>k<?n. p = (vx k, vy k) then
              let k = (SOME k. k < ?n \<and> p = (vx k, vy k)) in (vx (vtgt k), vy (vtgt k))
            else if \<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p = edge_pt i t \<and> \<not> is_canonical i then
              let (i,t) = (SOME (i,t). i < ?n \<and> 0 < t \<and> t < 1 \<and> p = edge_pt i t \<and> \<not> is_canonical i)
              in let j = partner i in
              if snd(scheme!i) = snd(scheme!j) then edge_pt j t else edge_pt j (1-t)
            else p)" for p
  \<comment> \<open>Y = image of P under q.\<close>
  define Y where "Y = q ` P"
  define TY where "TY = {U. \<exists>V. V \<subseteq> P \<and> (\<forall>x \<in> V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V) \<and> U = q ` V
      \<and> V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P}"
  \<comment> \<open>The 11 conditions need to be verified. Main challenges:
     C1 (polygonal region): regular n-gon is convex, n \\<ge> 3 by assumption.
     C2 (quotient map): q is continuous, surjective, TY is quotient topology.
     C3 (vertex distinctness): distinct angles give distinct points.
     C4 (vertices in P): vertices are in convex hull.
     C5 (P = convex hull): by definition.
     C6 (edge interiors don't intersect): convexity + distinct vertices.
     C8 (identification pattern): by construction of q.
     C9 (interior injectivity): q = id on interior.
     C10 (CCW orientation): regular polygon vertices are CCW.
     C11 (strict convexity): all vertices on one side of each edge.\<close>
  \<comment> \<open>C3: vertex distinctness. Distinct i,j < n give distinct angles, hence distinct (cos,sin).\<close>
  have hC3: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
  proof (intro allI impI)
    fix i j assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
    show "(vx i, vy i) \<noteq> (vx j, vy j)"
    proof
      assume heq: "(vx i, vy i) = (vx j, vy j)"
      hence "cos (2*pi*real i/real ?n) = cos (2*pi*real j/real ?n)"
        and "sin (2*pi*real i/real ?n) = sin (2*pi*real j/real ?n)"
        unfolding vx_def vy_def by (by100 auto)+
      from cos_sin_eq_imp[OF this]
      obtain k :: int where hk: "2*pi*real i/real ?n - 2*pi*real j/real ?n = real_of_int k * 2 * pi"
        by (by100 blast)
      have hpi_pos: "pi > 0" using pi_gt_zero .
      have hn_pos: "real ?n > 0" using assms by (by100 linarith)
      from hk have h_diff: "(real i - real j) / real ?n = real_of_int k"
      proof -
        from hk have "2*pi*real i/real ?n - 2*pi*real j/real ?n = real_of_int k * (2 * pi)"
          by (by100 simp)
        hence "2*pi * (real i/real ?n - real j/real ?n) = real_of_int k * (2 * pi)"
          using hn_pos by (simp add: diff_divide_distrib algebra_simps)
        hence "real i/real ?n - real j/real ?n = real_of_int k"
          using hpi_pos by (by100 simp)
        thus ?thesis using hn_pos by (simp add: diff_divide_distrib)
      qed
      hence "real i - real j = real_of_int k * real ?n"
        using hn_pos by (simp add: field_simps)
      hence "real_of_int (int i - int j) = real_of_int k * real ?n"
        by (by100 simp)
      \<comment> \<open>Since |i-j| < n and n > 0, the only integer k giving |k*n| < n is k = 0.\<close>
      hence hk0: "k = 0"
      proof -
        have "real_of_int (int i - int j) = real_of_int k * real ?n"
          using \<open>real i - real j = real_of_int k * real ?n\<close> by (by100 simp)
        have "\<bar>real_of_int (int i - int j)\<bar> < real ?n"
          using hi hj by (by100 simp)
        hence "\<bar>real_of_int k * real ?n\<bar> < real ?n"
          using \<open>real_of_int (int i - int j) = real_of_int k * real ?n\<close> by (by100 simp)
        hence "\<bar>real_of_int k\<bar> * real ?n < real ?n"
          using hn_pos by (simp add: abs_mult)
        hence "\<bar>real_of_int k\<bar> < 1"
          using hn_pos by (by100 simp)
        thus "k = 0" by (by100 linarith)
      qed
      hence "real i = real j" using \<open>(real i - real j)/real ?n = real_of_int k\<close> hn_pos
        by (by100 simp)
      hence "i = j" by (by100 simp)
      thus False using hij by (by100 simp)
    qed
  qed
  \<comment> \<open>C4: vertices in P (each vertex is a convex combination with coefficient 1 at position k).\<close>
  have hC4: "\<forall>i<?n. (vx i, vy i) \<in> P"
  proof (intro allI impI)
    fix k assume hk: "k < ?n"
    define coeffs :: "nat \<Rightarrow> real" where "coeffs j = (if j = k then 1 else 0)" for j
    have "\<forall>i<?n. coeffs i \<ge> 0" unfolding coeffs_def by (by100 simp)
    moreover have "(\<Sum>i<?n. coeffs i) = 1"
      unfolding coeffs_def using hk by (by100 simp)
    moreover have "vx k = (\<Sum>i<?n. coeffs i * vx i)"
    proof -
      have "(\<Sum>i<?n. coeffs i * vx i) = (\<Sum>i<?n. (if i=k then vx i else 0))"
        unfolding coeffs_def by (rule sum.cong) (by100 auto)+
      also have "\<dots> = vx k" using hk by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    moreover have "vy k = (\<Sum>i<?n. coeffs i * vy i)"
    proof -
      have "(\<Sum>i<?n. coeffs i * vy i) = (\<Sum>i<?n. (if i=k then vy i else 0))"
        unfolding coeffs_def by (rule sum.cong) (by100 auto)+
      also have "\<dots> = vy k" using hk by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    ultimately show "(vx k, vy k) \<in> P"
      unfolding P_def by (by100 blast)
  qed
  \<comment> \<open>C5: P = convex hull of vertices (by definition of P).\<close>
  have hC5: "P = {(x,y) | x y. \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0)
                   \<and> (\<Sum>i<?n. coeffs i) = 1
                   \<and> x = (\<Sum>i<?n. coeffs i * vx i)
                   \<and> y = (\<Sum>i<?n. coeffs i * vy i)}"
    unfolding P_def by (by100 simp)
  \<comment> \<open>C1: P is a polygonal region. Need: n \\<ge> 3, distinct vertices, no vertex in hull of others.\<close>
  \<comment> \<open>Extremality: no vertex is in convex hull of the others.\<close>
  have hextreme: "\<forall>k<?n. \<not> (\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
            \<and> (\<Sum>i<?n. coeffs i) = 1
            \<and> vx k = (\<Sum>i<?n. coeffs i * vx i) \<and> vy k = (\<Sum>i<?n. coeffs i * vy i))"
  proof (intro allI impI notI)
    fix k assume hk: "k < ?n"
    assume "\<exists>coeffs. (\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0) \<and> coeffs k = 0
            \<and> (\<Sum>i<?n. coeffs i) = 1
            \<and> vx k = (\<Sum>i<?n. coeffs i * vx i) \<and> vy k = (\<Sum>i<?n. coeffs i * vy i)"
    then obtain coeffs where
        hcoeff_pos: "\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0"
      and hk0: "coeffs k = 0"
      and hsum1: "(\<Sum>i<?n. coeffs i) = 1"
      and hvx: "vx k = (\<Sum>i<?n. coeffs i * vx i)"
      and hvy: "vy k = (\<Sum>i<?n. coeffs i * vy i)" by (by100 blast)
    \<comment> \<open>Dot product with radial direction of vertex k:
       d(k) = vx(k)*vx(k) + vy(k)*vy(k) = cos^2 + sin^2 = 1.
       For any other vertex i \\<noteq> k:
       d(i) = vx(k)*vx(i) + vy(k)*vy(i) = cos(2\\<pi>k/n)*cos(2\\<pi>i/n) + sin(2\\<pi>k/n)*sin(2\\<pi>i/n)
            = cos(2\\<pi>(k-i)/n) < 1 (since k \\<noteq> i mod n gives nonzero angle).\<close>
    define dot where "dot i = vx k * vx i + vy k * vy i" for i
    have hdk: "dot k = 1" unfolding dot_def vx_def vy_def
      using sin_cos_squared_add[of "2*pi*real k/real ?n"] by (by100 simp)
    \<comment> \<open>Convex combination of dot products equals dot product of convex combination.\<close>
    have "(\<Sum>i<?n. coeffs i * dot i) = vx k * (\<Sum>i<?n. coeffs i * vx i) + vy k * (\<Sum>i<?n. coeffs i * vy i)"
      unfolding dot_def by (simp add: sum_distrib_left algebra_simps sum.distrib)
    also have "\<dots> = vx k * vx k + vy k * vy k" using hvx hvy by (by100 simp)
    also have "\<dots> = 1" unfolding vx_def vy_def
      using sin_cos_squared_add[of "2*pi*real k/real ?n"] by (by100 simp)
    finally have hsum_dot: "(\<Sum>i<?n. coeffs i * dot i) = 1" .
    \<comment> \<open>But dot i < 1 for all i \\<noteq> k (cosine of nonzero angle).\<close>
    have hdot_lt: "\<forall>i<?n. i \<noteq> k \<longrightarrow> dot i < 1"
    proof (intro allI impI)
      fix i assume "i < ?n" "i \<noteq> k"
      have hn_pos': "real ?n > 0" using assms by (by100 linarith)
      have "dot i = cos (2*pi*real k/real ?n - 2*pi*real i/real ?n)"
        unfolding dot_def vx_def vy_def
        using cos_diff[of "2*pi*real k/real ?n" "2*pi*real i/real ?n"] by (by100 simp)
      also have "\<dots> = cos (2*pi*(real k - real i)/real ?n)"
        using hn_pos' by (simp add: diff_divide_distrib algebra_simps)
      finally have hdot_eq: "dot i = cos (2*pi*(real k - real i)/real ?n)" .
      \<comment> \<open>The angle 2\\<pi>(k-i)/n is not a multiple of 2\\<pi> (since 0 < |k-i| < n).\<close>
      have "cos (2*pi*(real k - real i)/real ?n) < 1"
      proof -
        \<comment> \<open>The angle \\<theta> = 2\\<pi>(k-i)/n is not a multiple of 2\\<pi>.\<close>
        have "real k - real i \<noteq> 0" using \<open>i \<noteq> k\<close> by (by100 simp)
        hence hangle_ne0: "2*pi*(real k - real i)/real ?n \<noteq> 0"
          using pi_gt_zero hn_pos' by (by100 simp)
        \<comment> \<open>|k-i| < n, so |\\<theta>| < 2\\<pi>. Hence \\<theta> is not a nonzero multiple of 2\\<pi>.\<close>
        have habs_diff: "\<bar>real k - real i\<bar> < real ?n" using \<open>i < ?n\<close> hk by (by100 simp)
        have "\<bar>2*pi*(real k - real i)/real ?n\<bar> = 2*pi * \<bar>real k - real i\<bar> / real ?n"
          using pi_gt_zero hn_pos' by (simp add: abs_mult)
        also have "\<dots> < 2*pi"
        proof -
          have "\<bar>real k - real i\<bar> / real ?n < real ?n / real ?n"
            using habs_diff hn_pos'
            by (intro divide_strict_right_mono) (by100 auto)+
          hence "\<bar>real k - real i\<bar> / real ?n < 1" using hn_pos' by (by100 simp)
          have h2pi: "2*pi > 0" using pi_gt_zero by (by100 simp)
          have "2*pi * (\<bar>real k - real i\<bar> / real ?n) < 2*pi * 1"
            using \<open>\<bar>real k - real i\<bar> / real ?n < 1\<close> h2pi
            by (rule mult_strict_left_mono)
          hence "2*pi * \<bar>real k - real i\<bar> / real ?n < 2*pi"
            by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        finally have habs_lt: "\<bar>2*pi*(real k - real i)/real ?n\<bar> < 2*pi" .
        \<comment> \<open>So \\<theta> \\<in> (-2\\<pi>, 2\\<pi>) \\<setminus> \\{0\\}. cos is < 1 on this set.\<close>
        \<comment> \<open>cos \\<le> 1 always. cos = 1 implies \\<theta> = 0 (modulo 2\\<pi>).\<close>
        let ?\<theta> = "2*pi*(real k - real i)/real ?n"
        have "cos ?\<theta> \<noteq> 1"
        proof
          assume hcos1: "cos ?\<theta> = 1"
          have hsin0: "sin ?\<theta> = 0"
          proof -
            from sin_cos_squared_add[of ?\<theta>]
            have "(sin ?\<theta>)\<^sup>2 = 1 - (cos ?\<theta>)\<^sup>2" by (by100 linarith)
            also have "\<dots> = 0" using hcos1 by (by100 simp)
            finally show ?thesis by (by100 simp)
          qed
          have hcos_eq: "cos 0 = cos ?\<theta>" using hcos1 by (by100 simp)
          have hsin_eq: "sin 0 = sin ?\<theta>" using hsin0 by (by100 simp)
          from cos_sin_eq_imp[OF hcos_eq hsin_eq]
          obtain kk :: int where hkk: "0 - ?\<theta> = real_of_int kk * 2 * pi" by (by100 blast)
          hence "?\<theta> = -(real_of_int kk) * (2*pi)" by (by100 linarith)
          hence "\<bar>real_of_int kk\<bar> * (2*pi) < 2*pi"
            using habs_lt by (simp add: abs_mult abs_minus_commute)
          hence "\<bar>real_of_int kk\<bar> < 1" using pi_gt_zero by (by100 simp)
          hence "kk = 0" by (by100 linarith)
          hence "?\<theta> = 0" using \<open>?\<theta> = -(real_of_int kk) * (2*pi)\<close> by (by100 simp)
          thus False using hangle_ne0 by (by100 simp)
        qed
        from this show ?thesis using cos_le_one[of ?\<theta>] by (by100 linarith)
      qed
      thus "dot i < 1" using hdot_eq by (by100 simp)
    qed
    \<comment> \<open>Since coeffs k = 0 and sum coeffs = 1, there exists i \\<noteq> k with coeffs i > 0.\<close>
    have "\<exists>i<?n. i \<noteq> k \<and> coeffs i > 0"
    proof (rule ccontr)
      assume "\<not> (\<exists>i<?n. i \<noteq> k \<and> coeffs i > 0)"
      hence "\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i \<le> 0" by (by100 auto)
      hence hall0: "\<forall>i<?n. i \<noteq> k \<longrightarrow> coeffs i = 0" using hcoeff_pos by (by100 force)
      hence "\<forall>i<?n. coeffs i = 0" using hk0 by (by100 force)
      hence "(\<Sum>i<?n. coeffs i) = 0" by (by100 simp)
      thus False using hsum1 by (by100 simp)
    qed
    \<comment> \<open>Then the weighted sum of dot products is < 1, contradicting = 1.\<close>
    then obtain i0 where hi0: "i0 < ?n" "i0 \<noteq> k" "coeffs i0 > 0" by (by100 blast)
    have "(\<Sum>i<?n. coeffs i * dot i) < (\<Sum>i<?n. coeffs i * 1)"
    proof -
      \<comment> \<open>Each term: coeffs i * dot i \\<le> coeffs i * 1 (since dot i \\<le> 1 and coeffs i \\<ge> 0).\<close>
      have hle: "\<forall>i<?n. coeffs i * dot i \<le> coeffs i * 1"
      proof (intro allI impI)
        fix i assume "i < ?n"
        show "coeffs i * dot i \<le> coeffs i * 1"
        proof (cases "i = k")
          case True thus ?thesis using hk0 by (by100 simp)
        next
          case False
          hence "coeffs i \<ge> 0" using hcoeff_pos \<open>i < ?n\<close> by (by100 blast)
          moreover have "dot i \<le> 1"
          proof -
            have "dot i = cos (2*pi*real k/real ?n - 2*pi*real i/real ?n)"
              unfolding dot_def vx_def vy_def
              using cos_diff[of "2*pi*real k/real ?n" "2*pi*real i/real ?n"] by (by100 simp)
            thus ?thesis using cos_le_one by (by100 simp)
          qed
          ultimately show ?thesis using mult_left_mono[of "dot i" 1 "coeffs i"] by (by100 simp)
        qed
      qed
      \<comment> \<open>The i0 term is strictly less: coeffs i0 * dot i0 < coeffs i0 * 1.\<close>
      have hdot_i0_lt: "dot i0 < 1" using hdot_lt hi0(1) hi0(2) by (by100 blast)
      have hstrict: "coeffs i0 * dot i0 < coeffs i0 * 1"
        using hi0(3) hdot_i0_lt by (by100 simp)
      \<comment> \<open>Sum with one strict and rest \\<le> gives strict overall.\<close>
      show ?thesis
        using sum_strict_mono_ex1[of "{..<(length scheme)}" "\<lambda>i. coeffs i * dot i" "\<lambda>i. coeffs i * 1"]
              hle hstrict hi0(1) by (by100 force)
    qed
    also have "\<dots> = 1" using hsum1 by (by100 simp)
    finally show False using hsum_dot by (by100 simp)
  qed
  have hC1: "top1_is_polygonal_region_on P ?n"
    unfolding top1_is_polygonal_region_on_def
    using assms hC3 hextreme hC5 by (by100 blast)
  \<comment> \<open>C10: CCW orientation. For regular polygon, cross product
     (v\\_i - centroid) \\<times> (v\\_{i+1} - centroid) = sin(2\\<pi>/n) > 0.\<close>
  \<comment> \<open>Centroid of regular n-gon is (0,0): sum of n-th roots of unity = 0.\<close>
  \<comment> \<open>Sum of n-th roots of unity = 0 (complex geometric series).
     Proof: cis(2\\<pi>k/n) = (cis(2\\<pi>/n))^k by DeMoivre.
     \\<Sum>k<n (cis(2\\<pi>/n))^k = (1 - (cis(2\\<pi>/n))^n)/(1 - cis(2\\<pi>/n)) = 0
     since (cis(2\\<pi>/n))^n = cis(2\\<pi>) = 1.\<close>
  \<comment> \<open>Prove \\<Sum>k<n. cis(2\\<pi>k/n) = 0 via geometric series, then extract Re/Im.\<close>
  have hn_pos: "real ?n > 0" using assms by (by100 linarith)
  have hsin_pos: "sin (2 * pi / real ?n) > 0"
  proof -
    have "2 * pi / real ?n > 0" using pi_gt_zero hn_pos by (by100 simp)
    moreover have "2 * pi / real ?n < pi"
    proof -
      have "real ?n \<ge> 3" using assms by (by100 simp)
      hence "2 * pi / real ?n \<le> 2 * pi / 3" using pi_gt_zero
        by (intro divide_left_mono) (by100 auto)+
      also have "\<dots> < pi" using pi_gt_zero by (by100 simp)
      finally show ?thesis .
    qed
    ultimately show ?thesis using sin_gt_zero by (by100 blast)
  qed
  have hroots: "(\<Sum>k<?n. cis (2*pi*real k/real ?n)) = (0 :: complex)"
  proof -
    let ?w = "cis (2*pi/real ?n) :: complex"
    \<comment> \<open>Each term is ?w^k.\<close>
    have hw_k: "\<And>k. ?w ^ k = cis (real k * (2*pi/real ?n))"
      using DeMoivre by (by100 blast)
    have hw_k': "\<And>k::nat. cis (2*pi*real k/real ?n) = ?w ^ k"
    proof -
      fix k :: nat
      have eq: "(2::real)*pi*real k/real ?n = real k * (2*pi/real ?n)"
        by (by100 algebra)
      show "cis (2*pi*real k/real ?n) = ?w ^ k"
        unfolding eq using hw_k[of k] by (by100 simp)
    qed
    have sum_eq: "(\<Sum>k<?n. cis (2*pi*real k/real ?n)) = (\<Sum>k<?n. ?w ^ k)"
      using hw_k' by (intro sum.cong) (by100 simp)+
    \<comment> \<open>?w^n = cis(2\\<pi>) = 1.\<close>
    have hw_n: "?w ^ ?n = 1"
    proof -
      have "?w ^ ?n = cis (real ?n * (2*pi/real ?n))" using DeMoivre by (by100 blast)
      also have "real ?n * (2*pi/real ?n) = 2*pi" using hn_pos by (by100 simp)
      also have "cis (2*pi) = 1"
        using cis_2pi by (by100 simp)
      finally show ?thesis .
    qed
    \<comment> \<open>?w \\<noteq> 1 (since 0 < 2\\<pi>/n < 2\\<pi>).\<close>
    have hw_ne1: "?w \<noteq> 1"
    proof
      assume "?w = 1"
      \<comment> \<open>cis(2\\<pi>/n)=1 implies 2\\<pi>/n = 2k\\<pi> for some integer k.
         Since 0 < 2\\<pi>/n < 2\\<pi> (for n\\<ge>3), only k=0 possible, giving 2\\<pi>/n=0, contradiction.\<close>
      hence "sin (2*pi/real ?n) = 0"
        by (simp add: complex_eq_iff cis.simps)
      thus False using hsin_pos by (by100 linarith)
    qed
    \<comment> \<open>Geometric series: (1 - ?w) * \\<Sum>k\\<le>n-1. ?w^k = 1 - ?w^n = 0.\<close>
    have "(1 - ?w) * (\<Sum>k\<le>?n - 1. ?w ^ k) = 1 - ?w ^ (Suc (?n - 1))"
      by (rule sum_gp_basic)
    also have "Suc (?n - 1) = ?n" using assms by (by100 simp)
    also have "1 - ?w ^ ?n = 0" using hw_n by (by100 simp)
    finally have "(1 - ?w) * (\<Sum>k\<le>?n - 1. ?w ^ k) = 0" .
    hence "(\<Sum>k\<le>?n - 1. ?w ^ k) = 0" using hw_ne1 by (by100 force)
    \<comment> \<open>Convert from {..n-1} to {..<n}.\<close>
    moreover have "{..?n - 1} = {..<?n}" using assms by (by100 auto)
    ultimately have "(\<Sum>k<?n. ?w ^ k) = 0" by (by100 simp)
    thus ?thesis using sum_eq by (by100 simp)
  qed
  have hcx0: "(\<Sum>j<?n. vx j) = 0"
  proof -
    have "(\<Sum>j<?n. vx j) = Re (\<Sum>j<?n. cis (2*pi*real j/real ?n))"
      unfolding vx_def by (simp add: Re_sum cis.simps)
    also have "\<dots> = Re 0" using hroots by (by100 simp)
    also have "\<dots> = 0" by (by100 simp)
    finally show ?thesis .
  qed
  have hcy0: "(\<Sum>j<?n. vy j) = 0"
  proof -
    have "(\<Sum>j<?n. vy j) = Im (\<Sum>j<?n. cis (2*pi*real j/real ?n))"
      unfolding vy_def by (simp add: Im_sum cis.simps)
    also have "\<dots> = Im 0" using hroots by (by100 simp)
    also have "\<dots> = 0" by (by100 simp)
    finally show ?thesis .
  qed
  \<comment> \<open>Cross product vx(i)*vy(i+1) - vy(i)*vx(i+1) = sin(2\\<pi>/n) for regular polygon.\<close>
  have hcross: "\<And>i. i < ?n \<Longrightarrow> vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n) = sin (2 * pi / real ?n)"
  proof -
    fix i assume hi: "i < ?n"
    let ?a = "2*pi*real i/real ?n"
    let ?b = "2*pi*real (Suc i mod ?n)/real ?n"
    have step1: "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n)
        = cos ?a * sin ?b - sin ?a * cos ?b" unfolding vx_def vy_def by (by100 simp)
    have step2: "cos ?a * sin ?b - sin ?a * cos ?b = sin (?b - ?a)"
      using sin_diff[of ?b ?a] by (by100 simp)
    \<comment> \<open>Key: ?b - ?a = 2\\<pi> * (Suc i mod n - i) / n = 2\\<pi>/n (or 2\\<pi>*(n-i+1?)/n for wraparound).\<close>
    have step3: "sin (?b - ?a) = sin (2*pi/real ?n)"
    proof (cases "Suc i < ?n")
      case True
      \<comment> \<open>i < n-1: Suc i mod n = Suc i, so b-a = 2\\<pi>(i+1)/n - 2\\<pi>i/n = 2\\<pi>/n.\<close>
      have "Suc i mod ?n = Suc i" using True by (by100 simp)
      hence "?b - ?a = 2*pi*(real (Suc i))/real ?n - 2*pi*real i/real ?n" by (by100 simp)
      also have "\<dots> = 2*pi/real ?n"
        using assms by (simp add: of_nat_Suc divide_simps algebra_simps)
      finally show ?thesis by (by100 simp)
    next
      case False
      \<comment> \<open>i = n-1: Suc i mod n = 0, b-a = -2\\<pi>(n-1)/n. sin(-2\\<pi>(n-1)/n) = sin(2\\<pi>/n).\<close>
      hence "i = ?n - 1" using hi by (by100 simp)
      hence "Suc i = ?n" using hi by (by100 simp)
      hence "Suc i mod ?n = 0" by (by100 simp)
      hence h_mod0: "Suc i mod ?n = 0" by (by100 simp)
      \<comment> \<open>Direct: sin(?b - ?a) = sin(-2\\<pi>*(n-1)/n) = sin(2\\<pi>/n).\<close>
      have hba_neg: "?b - ?a = - (2*pi*real i/real ?n)"
        using h_mod0 by (by100 simp)
      have "sin (?b - ?a) = - sin (2*pi*real i/real ?n)"
        unfolding hba_neg by (by100 simp)
      also have "\<dots> = - sin (2*pi*real (?n - 1)/real ?n)"
        using \<open>i = ?n - 1\<close> by (by100 simp)
      also have "\<dots> = - sin (2*pi - 2*pi/real ?n)"
        using assms by (simp add: divide_simps algebra_simps of_nat_diff)
      also have "\<dots> = sin (2*pi/real ?n)"
      proof -
        have "sin (2*pi - 2*pi/real ?n) = - sin (2*pi/real ?n)"
          using sin_minus[of "2*pi/real ?n"] by (simp add: sin_diff)
        thus ?thesis by (by100 simp)
      qed
      finally show ?thesis .
    qed
    show "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n) = sin (2*pi/real ?n)"
      using step1 step2 step3 by (by100 simp)
  qed
  \<comment> \<open>hsin\\_pos already proved above. hcross uses it for C10 assembly.\<close>
  have hC10: "\<forall>i<?n. let cx = (\<Sum>j<?n. vx j)/real ?n; cy = (\<Sum>j<?n. vy j)/real ?n
       in (vx i - cx)*(vy(Suc i mod ?n) - cy) - (vy i - cy)*(vx(Suc i mod ?n) - cx) > 0"
  proof (intro allI impI, unfold Let_def)
    fix i assume hi: "i < ?n"
    \<comment> \<open>Goal: (vx i - cx)*(vy(i+1) - cy) - (vy i - cy)*(vx(i+1) - cx) > 0, where cx=\\<Sum>vx/n, cy=\\<Sum>vy/n.\<close>
    have "(\<Sum>j<?n. vx j) / real ?n = 0" using hcx0 by (by100 simp)
    moreover have "(\<Sum>j<?n. vy j) / real ?n = 0" using hcy0 by (by100 simp)
    moreover have "vx i * vy(Suc i mod ?n) - vy i * vx(Suc i mod ?n) = sin (2*pi/real ?n)"
      using hcross[OF hi] .
    moreover note hsin_pos
    ultimately have h1: "(\<Sum>j<?n. vx j) / real ?n = 0"
      and h2: "(\<Sum>j<?n. vy j) / real ?n = 0"
      and h3: "vx i * vy(Suc i mod ?n) - vy i * vx(Suc i mod ?n) = sin (2*pi/real ?n)"
      and h4: "sin (2*pi/real ?n) > 0" by auto
    show "(vx i - (\<Sum>j<?n. vx j) / real ?n) *
       (vy (Suc i mod ?n) - (\<Sum>j<?n. vy j) / real ?n) -
       (vy i - (\<Sum>j<?n. vy j) / real ?n) *
       (vx (Suc i mod ?n) - (\<Sum>j<?n. vx j) / real ?n) > 0"
    proof -
      have "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n) > 0"
        using h3 h4 by (by100 linarith)
      moreover have "(vx i - (\<Sum>j<?n. vx j) / real ?n) *
         (vy (Suc i mod ?n) - (\<Sum>j<?n. vy j) / real ?n) -
         (vy i - (\<Sum>j<?n. vy j) / real ?n) *
         (vx (Suc i mod ?n) - (\<Sum>j<?n. vx j) / real ?n)
         = vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n)"
      proof -
        have "(\<Sum>j<?n. vx j) / real ?n = (0::real)" using h1 .
        moreover have "(\<Sum>j<?n. vy j) / real ?n = (0::real)" using h2 .
        ultimately have sx: "(\<Sum>j<?n. vx j) / real ?n = (0::real)"
          and sy: "(\<Sum>j<?n. vy j) / real ?n = (0::real)" by auto
        show ?thesis
          apply (subst sx)+
          apply (subst sy)+
          apply (simp only: diff_0_right mult_1_right)
          done
      qed
      ultimately show ?thesis by (by100 linarith)
    qed
  qed
  \<comment> \<open>C11: strict convexity. Every non-adjacent vertex is on the right of each edge.\<close>
  \<comment> \<open>C11 helper: the cross product for regular polygon vertices on the unit circle.
     For points at angles \\<alpha>, \\<beta>, \\<gamma> on the unit circle, the signed area of
     triangle (cos \\<alpha>, sin \\<alpha>), (cos \\<beta>, sin \\<beta>), (cos \\<gamma>, sin \\<gamma>) is
     (1/2)(sin(\\<beta>-\\<alpha>) + sin(\\<gamma>-\\<beta>) + sin(\\<alpha>-\\<gamma>)).
     We need: (cos \\<gamma> - cos \\<alpha>)(sin \\<beta> - sin \\<alpha>) - (sin \\<gamma> - sin \\<alpha>)(cos \\<beta> - cos \\<alpha>) < 0
     which equals sin(\\<beta>-\\<gamma>) + sin(\\<gamma>-\\<alpha>) - sin(\\<beta>-\\<alpha>).\<close>
  have cross_unit_circle:
    "\<And>a b c :: real. (cos c - cos a)*(sin b - sin a) - (sin c - sin a)*(cos b - cos a)
      = sin (b - c) + sin (c - a) - sin (b - a)"
  proof -
    fix a b c :: real
    \<comment> \<open>Expand LHS: cos(c)*sin(b) - cos(c)*sin(a) - cos(a)*sin(b) + cos(a)*sin(a)
       - sin(c)*cos(b) + sin(c)*cos(a) + sin(a)*cos(b) - sin(a)*cos(a)
       = [cos(c)*sin(b) - sin(c)*cos(b)]   = sin(b-c)
       + [sin(c)*cos(a) - cos(c)*sin(a)]   = sin(c-a)
       - [cos(a)*sin(b) - sin(a)*cos(b)]   = -sin(b-a)
       + [cos(a)*sin(a) - sin(a)*cos(a)]   = 0.\<close>
    have "cos c * sin b - sin c * cos b = sin (b - c)"
      using sin_diff[of b c] by (by100 simp)
    moreover have "sin c * cos a - cos c * sin a = sin (c - a)"
      using sin_diff[of c a] by (by100 simp)
    moreover have "cos a * sin b - sin a * cos b = sin (b - a)"
      using sin_diff[of b a] by (by100 simp)
    ultimately have h1: "sin (b - c) = cos c * sin b - sin c * cos b"
      and h2: "sin (c - a) = sin c * cos a - cos c * sin a"
      and h3: "sin (b - a) = cos a * sin b - sin a * cos b" by auto
    have expand: "(cos c - cos a)*(sin b - sin a) - (sin c - sin a)*(cos b - cos a)
      = cos c * sin b - cos c * sin a - cos a * sin b + cos a * sin a
      - (sin c * cos b - sin c * cos a - sin a * cos b + sin a * cos a)"
      by (by100 algebra)
    show "(cos c - cos a)*(sin b - sin a) - (sin c - sin a)*(cos b - cos a)
      = sin (b - c) + sin (c - a) - sin (b - a)"
      unfolding expand h1 h2 h3 by (by100 algebra)
  qed
  have hC11: "\<forall>i<?n. \<forall>k<?n.
        k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod ?n \<longrightarrow>
        (vx k - vx i)*(vy(Suc i mod ?n) - vy i) - (vy k - vy i)*(vx(Suc i mod ?n) - vx i) < 0"
  proof (intro allI impI)
    fix i k assume hi: "i < ?n" and hk: "k < ?n" and hki: "k \<noteq> i" and hki1: "k \<noteq> Suc i mod ?n"
    let ?\<alpha> = "2*pi*real i/real ?n"
    let ?\<beta> = "2*pi*real (Suc i mod ?n)/real ?n"
    let ?\<gamma> = "2*pi*real k/real ?n"
    have cross_eq: "(vx k - vx i)*(vy(Suc i mod ?n) - vy i) - (vy k - vy i)*(vx(Suc i mod ?n) - vx i)
        = sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>) - sin (?\<beta> - ?\<alpha>)"
    proof -
      have "(cos ?\<gamma> - cos ?\<alpha>)*(sin ?\<beta> - sin ?\<alpha>) - (sin ?\<gamma> - sin ?\<alpha>)*(cos ?\<beta> - cos ?\<alpha>)
          = sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>) - sin (?\<beta> - ?\<alpha>)"
        by (rule cross_unit_circle)
      thus ?thesis unfolding vx_def vy_def by (by100 simp)
    qed
    \<comment> \<open>sin(\\<beta>-\\<alpha>) = sin(2\\<pi>/n) from hcross.\<close>
    have hba: "sin (?\<beta> - ?\<alpha>) = sin (2*pi/real ?n)"
    proof -
      have "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n) = sin (2*pi/real ?n)"
        using hcross[OF hi] .
      moreover have "vx i * vy (Suc i mod ?n) - vy i * vx (Suc i mod ?n)
          = sin (?\<beta> - ?\<alpha>)"
        unfolding vx_def vy_def using sin_diff[of ?\<beta> ?\<alpha>] by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Apply sin\\_plus\\_sin: sin(\\<beta>-\\<gamma>) + sin(\\<gamma>-\\<alpha>)
       = 2*sin((\\<beta>-\\<alpha>)/2)*cos((\\<beta>+\\<alpha>-2\\<gamma>)/2).
       Since \\<beta>-\\<alpha> corresponds to 2\\<pi>/n, this gives
       = 2*sin(\\<pi>/n)*cos(something).\<close>
    have sum_eq: "sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>)
        = 2 * sin ((?\<beta> - ?\<alpha>)/2) * cos ((?\<beta> + ?\<alpha> - 2*?\<gamma>)/2)"
    proof -
      have "sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>)
          = 2 * sin (((?\<beta> - ?\<gamma>) + (?\<gamma> - ?\<alpha>))/2) * cos (((?\<beta> - ?\<gamma>) - (?\<gamma> - ?\<alpha>))/2)"
        by (rule sin_plus_sin)
      moreover have "((?\<beta> - ?\<gamma>) + (?\<gamma> - ?\<alpha>))/2 = (?\<beta> - ?\<alpha>)/2" by (by100 algebra)
      moreover have "((?\<beta> - ?\<gamma>) - (?\<gamma> - ?\<alpha>))/2 = (?\<beta> + ?\<alpha> - 2*?\<gamma>)/2" by (by100 algebra)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Also sin(2\\<pi>/n) = 2*sin(\\<pi>/n)*cos(\\<pi>/n).\<close>
    have double_angle: "sin (2*pi/real ?n) = 2 * sin (pi/real ?n) * cos (pi/real ?n)"
      using sin_double[of "pi/real ?n"] by (by100 simp)
    \<comment> \<open>Cleaner approach (no case split): use cos difference identity
       cos A - cos B = -2*sin((A+B)/2)*sin((A-B)/2)
       to get: cross = -4*sin((\\<beta>-\\<alpha>)/2)*sin((\\<beta>-\\<gamma>)/2)*sin((\\<alpha>-\\<gamma>)/2)
       Then show the product of three sines is positive.\<close>
    show "(vx k - vx i)*(vy(Suc i mod ?n) - vy i) - (vy k - vy i)*(vx(Suc i mod ?n) - vx i) < 0"
    proof -
      \<comment> \<open>Step 1: cross = sum - sin(\\<beta>-\\<alpha>) = 2*sin((\\<beta>-\\<alpha>)/2)*[cos bracket - cos half].\<close>
      have da2: "sin (?\<beta> - ?\<alpha>) = 2 * sin ((?\<beta> - ?\<alpha>)/2) * cos ((?\<beta> - ?\<alpha>)/2)"
      proof -
        have h2ne: "(2::real) \<noteq> 0" by (by100 simp)
        have h2x2: "(2::real) * ((?\<beta> - ?\<alpha>) / 2) = ?\<beta> - ?\<alpha>"
          using nonzero_mult_div_cancel_left[OF h2ne, of "?\<beta> - ?\<alpha>"] by (by100 simp)
        have "sin (2 * ((?\<beta> - ?\<alpha>) / 2)) = 2 * sin ((?\<beta> - ?\<alpha>) / 2) * cos ((?\<beta> - ?\<alpha>) / 2)"
          by (rule sin_double)
        thus ?thesis by (subst (asm) h2x2) (by100 assumption)
      qed
      have step2: "sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>) - sin (?\<beta> - ?\<alpha>)
        = 2 * sin ((?\<beta> - ?\<alpha>)/2) * (cos ((?\<beta> + ?\<alpha> - 2*?\<gamma>)/2) - cos ((?\<beta> - ?\<alpha>)/2))"
        using sum_eq da2 by (by100 algebra)
      \<comment> \<open>Step 2: Apply cos A - cos B = -2*sin((A+B)/2)*sin((A-B)/2).\<close>
      have cos_diff_eq: "cos ((?\<beta> + ?\<alpha> - 2*?\<gamma>)/2) - cos ((?\<beta> - ?\<alpha>)/2)
          = - 2 * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
      proof -
        define A where "A = (?\<beta> + ?\<alpha> - 2*?\<gamma>)/(2::real)"
        define B where "B = (?\<beta> - ?\<alpha>)/(2::real)"
        \<comment> \<open>cos A - cos B = 2*sin((A+B)/2)*sin((B-A)/2).\<close>
        have step: "cos A - cos B = 2 * sin ((A+B)/2) * sin ((B-A)/2)"
          unfolding A_def B_def by (rule cos_diff_cos)
        have eq1: "(A+B)/2 = (?\<beta> - ?\<gamma>)/2" unfolding A_def B_def by (by100 algebra)
        have eq2: "(B-A)/2 = (?\<gamma> - ?\<alpha>)/2" unfolding A_def B_def by (by100 algebra)
        have mid: "cos A - cos B = 2 * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<gamma> - ?\<alpha>)/2)"
          using step by (subst (asm) eq1, subst (asm) eq2) (by100 assumption)
        \<comment> \<open>sin((\\<gamma>-\\<alpha>)/2) = -sin((\\<alpha>-\\<gamma>)/2).\<close>
        have neg: "(?\<gamma> - ?\<alpha>)/2 = -((?\<alpha> - ?\<gamma>)/2)" by (by100 algebra)
        have "sin ((?\<gamma> - ?\<alpha>)/2) = - sin ((?\<alpha> - ?\<gamma>)/2)"
          by (subst neg, rule sin_minus)
        hence hsneg: "sin ((?\<gamma> - ?\<alpha>)/2) = - sin ((?\<alpha> - ?\<gamma>)/2)" .
        have "2 * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<gamma> - ?\<alpha>)/2)
            = - (2 * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2))"
          by (subst hsneg, simp only: mult_minus_right)
        with mid show ?thesis unfolding A_def B_def by (by100 linarith)
      qed
      \<comment> \<open>Step 3: cross = -4*sin((\\<beta>-\\<alpha>)/2)*sin((\\<beta>-\\<gamma>)/2)*sin((\\<alpha>-\\<gamma>)/2).\<close>
      have cross_product: "sin (?\<beta> - ?\<gamma>) + sin (?\<gamma> - ?\<alpha>) - sin (?\<beta> - ?\<alpha>)
        = - 4 * sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
        using step2 cos_diff_eq by (by100 algebra)
      \<comment> \<open>Step 4: Each sine is nonzero and the product is > 0.\<close>
      \<comment> \<open>sin((\\<beta>-\\<alpha>)/2) \\<noteq> 0: because \\<beta> \\<noteq> \\<alpha> (vertices i and i+1 are distinct).\<close>
      \<comment> \<open>sin((\\<beta>-\\<gamma>)/2) \\<noteq> 0: because \\<beta> \\<noteq> \\<gamma> (k \\<noteq> Suc i mod n).\<close>
      \<comment> \<open>sin((\\<alpha>-\\<gamma>)/2) \\<noteq> 0: because \\<alpha> \\<noteq> \\<gamma> (k \\<noteq> i).\<close>
      \<comment> \<open>Product positive: all three angles are multiples of \\<pi>/n in range (-\\<pi>,\\<pi>).
         The product of their signs is always positive (checked for all cases).\<close>
      have "sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2) > 0"
      proof -
        \<comment> \<open>Each angle is \\<pi>*m/n for some integer m with 0 < |m| < n.
           sin(\\<pi>*m/n) > 0 for 0 < m < n; sin(\\<pi>*m/n) < 0 for -n < m < 0.
           Product of signs is always (+) for non-adjacent vertices.\<close>
        \<comment> \<open>Factor 1: sin((\\<beta>-\\<alpha>)/2). Nonzero since vertices i and i+1 are distinct.\<close>
        \<comment> \<open>sin(\\<pi>*m/n) \\<noteq> 0 when 0 < |m| < n. Proof: sin = 0 iff angle = k\\<pi>.
           \\<pi>*m/n = k\\<pi> iff m = kn. Since |m| < n, k = 0, so m = 0. Contradiction.\<close>
        \<comment> \<open>Helper: sin(\\<pi>*m/n) \\<noteq> 0 for 0 < |m| < n (integer m, n \\<ge> 3).\<close>
        have sin_pi_frac_ne: "\<And>m::int. m \<noteq> 0 \<Longrightarrow> \<bar>m\<bar> < int ?n \<Longrightarrow>
            sin (pi * real_of_int m / real ?n) \<noteq> 0"
        proof -
          fix m :: int assume hm0: "m \<noteq> 0" and hm_bnd: "\<bar>m\<bar> < int ?n"
          show "sin (pi * real_of_int m / real ?n) \<noteq> 0"
          proof
            assume hsin0: "sin (pi * real_of_int m / real ?n) = 0"
            \<comment> \<open>By sin\\_zero\\_iff\\_int2: \\<exists>k. angle = k*\\<pi>.\<close>
            from hsin0[unfolded sin_zero_iff_int2]
            obtain kk :: int where hkk: "pi * real_of_int m / real ?n = real_of_int kk * pi"
              by (by100 blast)
            \<comment> \<open>Cancel \\<pi>: m/n = kk. Since |m| < n: |kk| < 1, so kk = 0, m = 0.\<close>
            \<comment> \<open>pi * m / n = kk * pi \\<Longrightarrow> m = kk * n.\<close>
            have "pi * real_of_int m = real_of_int kk * pi * real ?n"
              using hkk hn_pos by (simp add: field_simps)
            hence "real_of_int m = real_of_int kk * real ?n"
              using pi_gt_zero by (by100 simp)
            hence "\<bar>real_of_int m\<bar> = \<bar>real_of_int kk\<bar> * real ?n"
              using hn_pos by (simp add: abs_mult)
            hence "\<bar>real_of_int kk\<bar> * real ?n < real ?n"
              using hm_bnd by (by100 linarith)
            hence "\<bar>real_of_int kk\<bar> < 1" using hn_pos by (by100 simp)
            hence "kk = 0" by (by100 linarith)
            hence "real_of_int m = 0"
              using \<open>real_of_int m = real_of_int kk * real ?n\<close> by (by100 simp)
            thus False using hm0 by (by100 simp)
          qed
        qed
        \<comment> \<open>Apply sin\\_pi\\_frac\\_ne. Each angle = \\<pi>*(m)/n for integer m with 0<|m|<n.\<close>
        have hf1_ne: "sin ((?\<beta> - ?\<alpha>)/2) \<noteq> 0"
        proof -
          define m1 :: int where "m1 = int (Suc i mod ?n) - int i"
          have "Suc i mod ?n \<noteq> i"
          proof
            assume "Suc i mod ?n = i"
            hence "Suc i mod ?n = i mod ?n" using hi by (by100 simp)
            hence "Suc i mod ?n = i mod ?n" .
            hence "(Suc i - i) mod ?n = 0" using assms by (simp add: mod_eq_dvd_iff_nat)
            hence "?n dvd 1" by (by100 simp)
            thus False using assms by (by100 simp)
          qed
          hence hm1_ne: "m1 \<noteq> 0"
            unfolding m1_def by (by100 simp)
          have hm1_bnd: "\<bar>m1\<bar> < int ?n"
          proof -
            have "?n > 0" using assms by (by100 linarith)
            hence "Suc i mod ?n < ?n" by (by100 simp)
            thus ?thesis unfolding m1_def using hi by (by100 linarith)
          qed
          have hangle: "(?\<beta> - ?\<alpha>)/2 = pi * real_of_int m1 / real ?n"
            unfolding m1_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          show ?thesis unfolding hangle using sin_pi_frac_ne[OF hm1_ne hm1_bnd] .
        qed
        have hf2_ne: "sin ((?\<beta> - ?\<gamma>)/2) \<noteq> 0"
        proof -
          define m2 :: int where "m2 = int (Suc i mod ?n) - int k"
          have hm2_ne: "m2 \<noteq> 0"
            unfolding m2_def using hki1 by (by100 simp)
          have hm2_bnd: "\<bar>m2\<bar> < int ?n"
          proof -
            have "?n > 0" using assms by (by100 linarith)
            hence "Suc i mod ?n < ?n" by (by100 simp)
            thus ?thesis unfolding m2_def using hk by (by100 linarith)
          qed
          have hangle: "(?\<beta> - ?\<gamma>)/2 = pi * real_of_int m2 / real ?n"
            unfolding m2_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          show ?thesis unfolding hangle using sin_pi_frac_ne[OF hm2_ne hm2_bnd] .
        qed
        have hf3_ne: "sin ((?\<alpha> - ?\<gamma>)/2) \<noteq> 0"
        proof -
          define m3 :: int where "m3 = int i - int k"
          have hm3_ne: "m3 \<noteq> 0" using hki unfolding m3_def by (by100 simp)
          have hm3_bnd: "\<bar>m3\<bar> < int ?n" using hi hk unfolding m3_def by (by100 simp)
          have hangle: "(?\<alpha> - ?\<gamma>)/2 = pi * real_of_int m3 / real ?n"
            unfolding m3_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          show ?thesis unfolding hangle using sin_pi_frac_ne[OF hm3_ne hm3_bnd] .
        qed
        \<comment> \<open>Product of signs: for i<n-1 and k<i: (+)(+)(+). For k>i+1: (+)(-)(-).
           For i=n-1: (-)(-)( +). All give (+).\<close>
        \<comment> \<open>The sign of the product: each sin(\\<pi>m/n) has the same sign as m.
           Product of m1*m2*m3 > 0 in all cases.\<close>
        \<comment> \<open>Helper: sin(\\<pi>*m/n) > 0 for 0 < m < n (positive integer m).\<close>
        have sin_pi_frac_pos: "\<And>m::int. 0 < m \<Longrightarrow> m < int ?n \<Longrightarrow>
            sin (pi * real_of_int m / real ?n) > 0"
        proof -
          fix m :: int assume hm_pos: "0 < m" and hm_bnd: "m < int ?n"
          have "0 < pi * real_of_int m / real ?n"
            using pi_gt_zero hm_pos hn_pos by (by100 simp)
          moreover have "pi * real_of_int m / real ?n < pi"
          proof -
            have "real_of_int m / real ?n < 1" using hm_bnd hn_pos by (by100 simp)
            hence "pi * (real_of_int m / real ?n) < pi * 1"
              using pi_gt_zero by (rule mult_strict_left_mono)
            thus ?thesis by (by100 simp)
          qed
          ultimately show "sin (pi * real_of_int m / real ?n) > 0"
            using sin_gt_zero by (by100 blast)
        qed
        \<comment> \<open>Helper: sin(\\<pi>*m/n) < 0 for -n < m < 0 (negative integer m).\<close>
        have sin_pi_frac_neg: "\<And>m::int. m < 0 \<Longrightarrow> - int ?n < m \<Longrightarrow>
            sin (pi * real_of_int m / real ?n) < 0"
        proof -
          fix m :: int assume hm_neg: "m < 0" and hm_bnd: "- int ?n < m"
          have "sin (pi * real_of_int m / real ?n) = sin (- (pi * real_of_int (-m) / real ?n))"
            by (by100 simp)
          also have "\<dots> = - sin (pi * real_of_int (-m) / real ?n)"
            by (rule sin_minus)
          also have "\<dots> < 0"
          proof -
            have "0 < -m" using hm_neg by (by100 simp)
            moreover have "-m < int ?n" using hm_bnd by (by100 simp)
            ultimately have "sin (pi * real_of_int (-m) / real ?n) > 0"
              by (rule sin_pi_frac_pos)
            thus ?thesis by (by100 linarith)
          qed
          finally show "sin (pi * real_of_int m / real ?n) < 0" .
        qed
        \<comment> \<open>Now compute the sign of each factor.\<close>
        have sign_pos: "sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2) > 0"
        proof -
          \<comment> \<open>Re-derive angle matching (same as in hf\\_ne proofs).\<close>
          define m1 :: int where "m1 = int (Suc i mod ?n) - int i"
          define m2 :: int where "m2 = int (Suc i mod ?n) - int k"
          define m3 :: int where "m3 = int i - int k"
          have ha1: "(?\<beta> - ?\<alpha>)/2 = pi * real_of_int m1 / real ?n"
            unfolding m1_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          have ha2: "(?\<beta> - ?\<gamma>)/2 = pi * real_of_int m2 / real ?n"
            unfolding m2_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          have ha3: "(?\<alpha> - ?\<gamma>)/2 = pi * real_of_int m3 / real ?n"
            unfolding m3_def using hn_pos by (simp add: divide_simps of_int_diff algebra_simps)
          \<comment> \<open>Bounds on mi.\<close>
          have hn_gt0: "?n > 0" using assms by (by100 linarith)
          have hmod_lt: "Suc i mod ?n < ?n" using hn_gt0 by (by100 simp)
          have hm1_bnd: "- int ?n < m1 \<and> m1 < int ?n" unfolding m1_def using hi hmod_lt by (by100 linarith)
          have hm2_bnd: "- int ?n < m2 \<and> m2 < int ?n" unfolding m2_def using hk hmod_lt by (by100 linarith)
          have hm3_bnd: "- int ?n < m3 \<and> m3 < int ?n" unfolding m3_def using hi hk by (by100 linarith)
          \<comment> \<open>Show m1*m2*m3 > 0 by case split on signs.\<close>
          have hm_prod_pos: "m1 * m2 * m3 > 0"
          proof (cases "Suc i < ?n")
            case True \<comment> \<open>i < n-1: m1 = 1.\<close>
            hence "Suc i mod ?n = Suc i" by (by100 simp)
            hence hm1_eq: "m1 = 1" unfolding m1_def by (by100 simp)
            \<comment> \<open>k < i or k > i+1. In both cases (i+1-k)*(i-k) > 0.\<close>
            have "m2 * m3 > 0"
            proof -
              have "m2 = int (Suc i) - int k" unfolding m2_def using True by (by100 simp)
              hence "m2 = m3 + 1" unfolding m3_def by (by100 linarith)
              \<comment> \<open>m3 \\<noteq> 0 (k \\<noteq> i), m2 \\<noteq> 0 (k \\<noteq> i+1). m2 = m3+1, so both same sign or one is 0.\<close>
              have "m3 \<noteq> 0" unfolding m3_def using hki by (by100 simp)
              have "m2 \<noteq> 0" unfolding m2_def using hki1 True by (by100 simp)
              \<comment> \<open>m2 = m3+1. If m3 > 0: m2 > 0. If m3 < 0 and m3 \\<noteq> -1: m2 < 0.\<close>
              \<comment> \<open>m3 = -1 would mean k = i+1, but k \\<noteq> Suc i = Suc i mod n. Contradiction.\<close>
              have "m3 \<noteq> -1"
              proof
                assume "m3 = -1"
                hence "int k = int i + 1" unfolding m3_def by (by100 linarith)
                hence "k = Suc i" by (by100 simp)
                hence "k = Suc i mod ?n" using True by (by100 simp)
                thus False using hki1 by (by100 simp)
              qed
              \<comment> \<open>m2 = m3+1, m3 \\<noteq> 0, m3 \\<noteq> -1: either both > 0 or both < 0.\<close>
              show ?thesis
              proof (cases "m3 > 0")
                case True hence "m2 > 0" using \<open>m2 = m3 + 1\<close> by (by100 linarith)
                thus ?thesis using True by (by100 simp)
              next
                case False hence "m3 < 0" using \<open>m3 \<noteq> 0\<close> by (by100 linarith)
                hence "m3 < -1" using \<open>m3 \<noteq> -1\<close> by (by100 linarith)
                hence "m2 < 0" using \<open>m2 = m3 + 1\<close> by (by100 linarith)
                thus ?thesis using \<open>m3 < 0\<close> mult_neg_neg[of m2 m3] by (by100 linarith)
              qed
            qed
            thus ?thesis using hm1_eq by (by100 simp)
          next
            case False \<comment> \<open>i = n-1.\<close>
            hence hi_eq: "i = ?n - 1" using hi by (by100 simp)
            hence "Suc i mod ?n = 0" using hn_gt0 by (by100 simp)
            hence hm1_neg: "m1 = - int (?n - 1)" unfolding m1_def using hi_eq by (by100 simp)
            hence "m1 < 0" using assms by (by100 linarith)
            have hm2_neg: "m2 = - int k" unfolding m2_def using \<open>Suc i mod ?n = 0\<close> by (by100 simp)
            have "k \<noteq> 0" using hki1 \<open>Suc i mod ?n = 0\<close> by (by100 simp)
            hence "m2 < 0" using hm2_neg hk by (by100 linarith)
            have hm3_pos: "m3 = int (?n - 1) - int k" unfolding m3_def using hi_eq by (by100 simp)
            have "k \<noteq> ?n - 1" using hki hi_eq by (by100 simp)
            hence "k < ?n - 1" using hk by (by100 linarith)
            hence "m3 > 0" using hm3_pos by (by100 linarith)
            have "m1 * m2 > 0" using \<open>m1 < 0\<close> \<open>m2 < 0\<close> mult_neg_neg[of m1 m2]
              by (by100 linarith)
            thus ?thesis using \<open>m3 > 0\<close> by (by100 simp)
          qed
          \<comment> \<open>Each factor: sin(\\<pi>*mi/n) has the sign of mi.\<close>
          \<comment> \<open>Sign matching: for each factor, mi > 0 gives sin > 0; mi < 0 gives sin < 0.\<close>
          have hm1_ne: "m1 \<noteq> 0" using hf1_ne unfolding ha1
            using sin_pi_frac_ne[of m1] hm1_bnd by (by100 force)
          have hm2_ne: "m2 \<noteq> 0" using hf2_ne unfolding ha2
            using sin_pi_frac_ne[of m2] hm2_bnd by (by100 force)
          have hm3_ne: "m3 \<noteq> 0" using hf3_ne unfolding ha3
            using sin_pi_frac_ne[of m3] hm3_bnd by (by100 force)
          have s1: "sgn (sin ((?\<beta> - ?\<alpha>)/2)) = sgn m1"
          proof (cases "m1 > 0")
            case True thus ?thesis unfolding ha1
              using sin_pi_frac_pos[OF True] hm1_bnd by (by100 simp)
          next
            case False hence "m1 < 0" using hm1_ne by (by100 linarith)
            thus ?thesis unfolding ha1
              using sin_pi_frac_neg[of m1] hm1_bnd by (by100 simp)
          qed
          have s2: "sgn (sin ((?\<beta> - ?\<gamma>)/2)) = sgn m2"
          proof (cases "m2 > 0")
            case True thus ?thesis unfolding ha2
              using sin_pi_frac_pos[OF True] hm2_bnd by (by100 simp)
          next
            case False hence "m2 < 0" using hm2_ne by (by100 linarith)
            thus ?thesis unfolding ha2
              using sin_pi_frac_neg[of m2] hm2_bnd by (by100 simp)
          qed
          have s3: "sgn (sin ((?\<alpha> - ?\<gamma>)/2)) = sgn m3"
          proof (cases "m3 > 0")
            case True thus ?thesis unfolding ha3
              using sin_pi_frac_pos[OF True] hm3_bnd by (by100 simp)
          next
            case False hence "m3 < 0" using hm3_ne by (by100 linarith)
            thus ?thesis unfolding ha3
              using sin_pi_frac_neg[of m3] hm3_bnd by (by100 simp)
          qed
          \<comment> \<open>Product of sines has same sign as product of mi.\<close>
          \<comment> \<open>Product of sines: directly case-split on sign of each mi.\<close>
          have "sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2) > 0"
          proof (cases "m1 > 0")
            case hm1p: True
            hence hs1: "sin ((?\<beta> - ?\<alpha>)/2) > 0" unfolding ha1
              using sin_pi_frac_pos[OF hm1p] hm1_bnd by (by100 linarith)
            show ?thesis
            proof (cases "m2 > 0")
              case hm2p: True
              hence hs2: "sin ((?\<beta> - ?\<gamma>)/2) > 0" unfolding ha2
                using sin_pi_frac_pos[OF hm2p] hm2_bnd by (by100 linarith)
              have "m1 * m2 > 0" using hm1p hm2p by (by100 simp)
              have "m3 > 0"
              proof (rule ccontr)
                assume "\<not> m3 > 0"
                hence "m3 \<le> 0" by (by100 simp)
                hence "m1 * m2 * m3 \<le> 0" using \<open>m1 * m2 > 0\<close>
                  using mult_nonneg_nonpos[of "m1*m2" m3] by (by100 linarith)
                thus False using hm_prod_pos by (by100 linarith)
              qed
              hence hs3: "sin ((?\<alpha> - ?\<gamma>)/2) > 0" unfolding ha3
                using sin_pi_frac_pos[of m3] hm3_bnd by (by100 linarith)
              define sp where "sp = sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
              have "sp > 0" unfolding sp_def
                using hs2 hs3 mult_pos_pos[of "sin ((?\<beta> - ?\<gamma>)/2)" "sin ((?\<alpha> - ?\<gamma>)/2)"]
                by (by100 linarith)
              hence "sin ((?\<beta> - ?\<alpha>)/2) * sp > 0"
                using hs1 mult_pos_pos[of "sin ((?\<beta> - ?\<alpha>)/2)" sp] by (by100 linarith)
              thus ?thesis unfolding sp_def by (simp add: mult.assoc)
            next
              case hm2n: False hence "m2 < 0" using hm2_ne by (by100 linarith)
              hence hs2: "sin ((?\<beta> - ?\<gamma>)/2) < 0" unfolding ha2
                using sin_pi_frac_neg[of m2] hm2_bnd by (by100 linarith)
              have "m1 * m2 < 0" using hm1p \<open>m2 < 0\<close>
                using mult_pos_neg[of m1 m2] by (by100 linarith)
              have "m3 < 0"
              proof (rule ccontr)
                assume "\<not> m3 < 0"
                hence "m3 \<ge> 0" by (by100 simp)
                hence "m1 * m2 * m3 \<le> 0" using \<open>m1 * m2 < 0\<close>
                  using mult_nonpos_nonneg[of "m1*m2" m3] by (by100 linarith)
                thus False using hm_prod_pos by (by100 linarith)
              qed
              hence hs3: "sin ((?\<alpha> - ?\<gamma>)/2) < 0" unfolding ha3
                using sin_pi_frac_neg[of m3] hm3_bnd by (by100 linarith)
              define s23 where "s23 = sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
              have "s23 > 0" unfolding s23_def
                using hs2 hs3 mult_neg_neg[of "sin ((?\<beta> - ?\<gamma>)/2)" "sin ((?\<alpha> - ?\<gamma>)/2)"]
                by (by100 linarith)
              hence "sin ((?\<beta> - ?\<alpha>)/2) * s23 > 0"
                using hs1 mult_pos_pos[of "sin ((?\<beta> - ?\<alpha>)/2)" s23] by (by100 linarith)
              thus ?thesis unfolding s23_def by (simp add: mult.assoc)
            qed
          next
            case hm1n: False hence "m1 < 0" using hm1_ne by (by100 linarith)
            hence hs1: "sin ((?\<beta> - ?\<alpha>)/2) < 0" unfolding ha1
              using sin_pi_frac_neg[of m1] hm1_bnd by (by100 linarith)
            \<comment> \<open>m1 < 0 and m1*m2*m3 > 0: either m2>0,m3<0 or m2<0,m3>0.\<close>
            show ?thesis
            proof (cases "m2 > 0")
              case hm2p: True
              hence hs2: "sin ((?\<beta> - ?\<gamma>)/2) > 0" unfolding ha2
                using sin_pi_frac_pos[OF hm2p] hm2_bnd by (by100 linarith)
              have "m1 * m2 < 0" using \<open>m1 < 0\<close> hm2p
                using mult_neg_pos[of m1 m2] by (by100 linarith)
              have "m3 < 0"
              proof (rule ccontr)
                assume "\<not> m3 < 0" hence "m3 \<ge> 0" by (by100 simp)
                hence "m1 * m2 * m3 \<le> 0" using \<open>m1 * m2 < 0\<close>
                  using mult_nonpos_nonneg[of "m1*m2" m3] by (by100 linarith)
                thus False using hm_prod_pos by (by100 linarith)
              qed
              hence hs3: "sin ((?\<alpha> - ?\<gamma>)/2) < 0" unfolding ha3
                using sin_pi_frac_neg[of m3] hm3_bnd by (by100 linarith)
              define sp where "sp = sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<alpha> - ?\<gamma>)/2)"
              have "sp > 0" unfolding sp_def
                using hs1 hs3 mult_neg_neg[of "sin ((?\<beta> - ?\<alpha>)/2)" "sin ((?\<alpha> - ?\<gamma>)/2)"]
                by (by100 linarith)
              hence "sp * sin ((?\<beta> - ?\<gamma>)/2) > 0"
                using hs2 mult_pos_pos[of sp "sin ((?\<beta> - ?\<gamma>)/2)"] by (by100 linarith)
              thus ?thesis unfolding sp_def by (simp add: mult.assoc mult.commute mult.left_commute)
            next
              case hm2n: False hence "m2 < 0" using hm2_ne by (by100 linarith)
              hence hs2: "sin ((?\<beta> - ?\<gamma>)/2) < 0" unfolding ha2
                using sin_pi_frac_neg[of m2] hm2_bnd by (by100 linarith)
              have "m1 * m2 > 0" using \<open>m1 < 0\<close> \<open>m2 < 0\<close>
                using mult_neg_neg[of m1 m2] by (by100 linarith)
              have "m3 > 0"
              proof (rule ccontr)
                assume "\<not> m3 > 0" hence "m3 \<le> 0" by (by100 simp)
                hence "m1 * m2 * m3 \<le> 0" using \<open>m1 * m2 > 0\<close>
                  using mult_nonneg_nonpos[of "m1*m2" m3] by (by100 linarith)
                thus False using hm_prod_pos by (by100 linarith)
              qed
              hence hs3: "sin ((?\<alpha> - ?\<gamma>)/2) > 0" unfolding ha3
                using sin_pi_frac_pos[of m3] hm3_bnd by (by100 linarith)
              define sp where "sp = sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2)"
              have "sp > 0" unfolding sp_def
                using hs1 hs2 mult_neg_neg[of "sin ((?\<beta> - ?\<alpha>)/2)" "sin ((?\<beta> - ?\<gamma>)/2)"]
                by (by100 linarith)
              hence "sp * sin ((?\<alpha> - ?\<gamma>)/2) > 0"
                using hs3 mult_pos_pos[of sp "sin ((?\<alpha> - ?\<gamma>)/2)"] by (by100 linarith)
              thus ?thesis unfolding sp_def by (simp add: mult.assoc)
            qed
          qed
          thus ?thesis .
        qed
        thus ?thesis .
      qed
      hence "- 4 * sin ((?\<beta> - ?\<alpha>)/2) * sin ((?\<beta> - ?\<gamma>)/2) * sin ((?\<alpha> - ?\<gamma>)/2) < 0"
        by (by100 linarith)
      thus ?thesis using cross_eq cross_product by (by100 linarith)
    qed
  qed
  \<comment> \<open>C6: non-adjacent edge interiors don't intersect (strict convexity implies this).\<close>
  \<comment> \<open>C6: non-adjacent edge interiors don't intersect. Follows from C11.\<close>
  define open01 :: "real set" where "open01 = {0<..<1}"
  have hC6: "\<forall>i<?n. \<forall>j<?n.
        i \<noteq> j \<longrightarrow> (Suc i mod ?n) \<noteq> j \<longrightarrow> i \<noteq> (Suc j mod ?n) \<longrightarrow>
        (\<forall>s\<in>open01. \<forall>t\<in>open01.
           ((1 - s) * vx i + s * vx (Suc i mod ?n),
            (1 - s) * vy i + s * vy (Suc i mod ?n))
         \<noteq> ((1 - t) * vx j + t * vx (Suc j mod ?n),
             (1 - t) * vy j + t * vy (Suc j mod ?n)))"
  proof (intro allI impI ballI)
    fix i j s t
    assume hi: "i < ?n" and hj: "j < ?n" and hij: "i \<noteq> j"
       and hij1: "(Suc i mod ?n) \<noteq> j" and hji1: "i \<noteq> (Suc j mod ?n)"
       and hs: "s \<in> open01" and ht: "t \<in> open01"
    have hs01: "0 < s" "s < 1" using hs unfolding open01_def by (by100 auto)+
    have ht01: "0 < t" "t < 1" using ht unfolding open01_def by (by100 auto)+
    \<comment> \<open>Proof by contradiction: assume edges i and j have a common interior point p.\<close>
    show "((1 - s) * vx i + s * vx (Suc i mod ?n),
            (1 - s) * vy i + s * vy (Suc i mod ?n))
         \<noteq> ((1 - t) * vx j + t * vx (Suc j mod ?n),
             (1 - t) * vy j + t * vy (Suc j mod ?n))"
    proof
      assume heq: "((1 - s) * vx i + s * vx (Suc i mod ?n),
            (1 - s) * vy i + s * vy (Suc i mod ?n))
         = ((1 - t) * vx j + t * vx (Suc j mod ?n),
             (1 - t) * vy j + t * vy (Suc j mod ?n))"
      \<comment> \<open>Let p = the common point. p is on edge i (param s) and edge j (param t).\<close>
      \<comment> \<open>Cross product of (p - v\\_i) with (v\\_{i+1} - v\\_i):
         From edge i: p - v\\_i = s*(v\\_{i+1} - v\\_i), so cross = 0.
         From edge j: cross = (1-t)*C11(j) + t*C11(j+1) < 0. Contradiction.\<close>
      \<comment> \<open>Step 1: C11 gives cross(j,i) < 0 and cross(j+1,i) < 0.\<close>
      have hj_ne_i: "j \<noteq> i" using hij by (by100 simp)
      have hj_ne_i1: "j \<noteq> Suc i mod ?n" using hij1 by (by100 simp)
      have hj1_ne_i: "Suc j mod ?n \<noteq> i" using hji1 by (by100 simp)
      have hj1_ne_i1: "Suc j mod ?n \<noteq> Suc i mod ?n"
      proof
        assume "Suc j mod ?n = Suc i mod ?n"
        hence "Suc j mod ?n = Suc i mod ?n" .
        \<comment> \<open>Since j < n and i < n: Suc j < 2n and Suc i < 2n.
           Suc j mod n = Suc i mod n implies either Suc j = Suc i or |Suc j - Suc i| = n.\<close>
        have "j < ?n" "i < ?n" using hi hj by auto
        hence "Suc j \<le> ?n" "Suc i \<le> ?n" by auto
        \<comment> \<open>If Suc j \\<le> n and Suc i \\<le> n, and mod n equal: Suc j = Suc i (only possible).\<close>
        have "j = i"
        proof (cases "Suc j < ?n")
          case True hence "Suc j mod ?n = Suc j" by (by100 simp)
          show ?thesis
          proof (cases "Suc i < ?n")
            case True2: True hence "Suc i mod ?n = Suc i" by (by100 simp)
            from \<open>Suc j mod ?n = Suc i mod ?n\<close> True \<open>Suc j mod ?n = Suc j\<close> True2 \<open>Suc i mod ?n = Suc i\<close>
            show ?thesis by (by100 simp)
          next
            case False hence "Suc i = ?n" using \<open>Suc i \<le> ?n\<close> by (by100 linarith)
            hence "Suc i mod ?n = 0" by (by100 simp)
            from \<open>Suc j mod ?n = Suc i mod ?n\<close> \<open>Suc j mod ?n = Suc j\<close> this
            have "Suc j = 0" by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
        next
          case False hence "Suc j = ?n" using \<open>Suc j \<le> ?n\<close> by (by100 linarith)
          hence "Suc j mod ?n = 0" by (by100 simp)
          show ?thesis
          proof (cases "Suc i < ?n")
            case True hence "Suc i mod ?n = Suc i" by (by100 simp)
            from \<open>Suc j mod ?n = Suc i mod ?n\<close> \<open>Suc j mod ?n = 0\<close> this
            have "Suc i = 0" by (by100 simp)
            thus ?thesis by (by100 simp)
          next
            case False hence "Suc i = ?n" using \<open>Suc i \<le> ?n\<close> by (by100 linarith)
            from \<open>Suc j = ?n\<close> this show ?thesis by (by100 simp)
          qed
        qed
        thus False using hij by (by100 simp)
      qed
      have hn_gt0: "?n > 0" using assms by (by100 linarith)
      have hj1_lt: "Suc j mod ?n < ?n" using hn_gt0 by (by100 simp)
      \<comment> \<open>Apply C11 to vertices j and Suc j mod n.\<close>
      have hcross_j: "(vx j - vx i)*(vy(Suc i mod ?n) - vy i) - (vy j - vy i)*(vx(Suc i mod ?n) - vx i) < 0"
        using hC11 hi hj hj_ne_i hj_ne_i1 by (by100 blast)
      have hcross_j1: "(vx(Suc j mod ?n) - vx i)*(vy(Suc i mod ?n) - vy i) - (vy(Suc j mod ?n) - vy i)*(vx(Suc i mod ?n) - vx i) < 0"
        using hC11 hi hj1_lt hj1_ne_i hj1_ne_i1 by (by100 blast)
      \<comment> \<open>Step 2: cross((1-t)*v\\_j + t*v\\_{j+1} - v\\_i, v\\_{i+1} - v\\_i) < 0.\<close>
      define dx where "dx = vx(Suc i mod ?n) - vx i"
      define dy where "dy = vy(Suc i mod ?n) - vy i"
      have cross_j_eq: "(vx j - vx i)*dy - (vy j - vy i)*dx < 0"
        using hcross_j unfolding dx_def dy_def .
      have cross_j1_eq: "(vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx < 0"
        using hcross_j1 unfolding dx_def dy_def .
      \<comment> \<open>The point from edge j: (1-t)*v\\_j + t*v\\_{j+1}. Its cross product with edge i direction:\<close>
      have cross_p_from_j:
        "((1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i))*dy
       - ((1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i))*dx < 0"
      proof -
        \<comment> \<open>Expand: ((1-t)*a + t*b)*dy - ((1-t)*c + t*d)*dx
           = (1-t)*(a*dy - c*dx) + t*(b*dy - d*dx).\<close>
        have expand: "((1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i))*dy
           - ((1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i))*dx
           = (1-t)*((vx j - vx i)*dy - (vy j - vy i)*dx)
           + t*((vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx)"
          by (by100 algebra)
        have "(1-t) > 0" using ht01 by (by100 linarith)
        moreover have "t > 0" using ht01 by (by100 linarith)
        moreover have "(vx j - vx i)*dy - (vy j - vy i)*dx < 0" using cross_j_eq .
        moreover have "(vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx < 0" using cross_j1_eq .
        ultimately have h_neg1: "(1-t)*((vx j - vx i)*dy - (vy j - vy i)*dx) < 0"
          and h_neg2: "t*((vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx) < 0"
          using mult_pos_neg[of "1-t" "(vx j - vx i)*dy - (vy j - vy i)*dx"]
                mult_pos_neg[of t "(vx(Suc j mod ?n) - vx i)*dy - (vy(Suc j mod ?n) - vy i)*dx"]
          by (by100 linarith)+
        thus ?thesis using expand by (by100 linarith)
      qed
      \<comment> \<open>Step 3: The same point is on edge i: p - v\\_i = s*(v\\_{i+1} - v\\_i).\<close>
      \<comment> \<open>From heq: (1-s)*vx i + s*vx(i+1) = (1-t)*vx j + t*vx(j+1).
         So: (1-t)*(vx j - vx i) + t*(vx(j+1) - vx i) = s*(vx(i+1) - vx i) = s*dx.
         Similarly for vy.\<close>
      have heqx: "(1-s)*vx i + s*vx(Suc i mod ?n) = (1-t)*vx j + t*vx(Suc j mod ?n)"
      proof -
        from heq have "fst ((1-s)*vx i + s*vx(Suc i mod ?n), (1-s)*vy i + s*vy(Suc i mod ?n))
            = fst ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))"
          by (by100 simp)
        thus ?thesis by (by100 simp)
      qed
      have heqy: "(1-s)*vy i + s*vy(Suc i mod ?n) = (1-t)*vy j + t*vy(Suc j mod ?n)"
      proof -
        from heq have "snd ((1-s)*vx i + s*vx(Suc i mod ?n), (1-s)*vy i + s*vy(Suc i mod ?n))
            = snd ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))"
          by (by100 simp)
        thus ?thesis by (by100 simp)
      qed
      have px_eq: "(1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i) = s * dx"
      proof -
        have "(1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i)
            = (1-t)*vx j + t*vx(Suc j mod ?n) - vx i" by (by100 algebra)
        also have "\<dots> = (1-s)*vx i + s*vx(Suc i mod ?n) - vx i" using heqx by (by100 linarith)
        also have "\<dots> = s*(vx(Suc i mod ?n) - vx i)" by (by100 algebra)
        finally show ?thesis unfolding dx_def by (by100 simp)
      qed
      have py_eq: "(1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i) = s * dy"
      proof -
        have "(1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i)
            = (1-t)*vy j + t*vy(Suc j mod ?n) - vy i" by (by100 algebra)
        also have "\<dots> = (1-s)*vy i + s*vy(Suc i mod ?n) - vy i" using heqy by (by100 linarith)
        also have "\<dots> = s*(vy(Suc i mod ?n) - vy i)" by (by100 algebra)
        finally show ?thesis unfolding dy_def by (by100 simp)
      qed
      \<comment> \<open>Substituting: s*dx*dy - s*dy*dx = 0. But from cross\\_p: should be < 0.\<close>
      \<comment> \<open>From px\\_eq and py\\_eq: the cross\\_p expression equals s*dx*dy - s*dy*dx = 0.\<close>
      have "((1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i))*dy
         - ((1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i))*dx
         = s*dx*dy - s*dy*dx"
        using px_eq py_eq by (by100 algebra)
      also have "\<dots> = 0" by (by100 algebra)
      finally have "((1-t)*(vx j - vx i) + t*(vx(Suc j mod ?n) - vx i))*dy
         - ((1-t)*(vy j - vy i) + t*(vy(Suc j mod ?n) - vy i))*dx = 0" .
      \<comment> \<open>But cross\\_p\\_from\\_j says this is < 0. Contradiction.\<close>
      thus False using cross_p_from_j by (by100 linarith)
    qed
  qed
  \<comment> \<open>General: interior point of any edge is not a vertex. Uses C11 + C3.\<close>
  have hnotvertex_gen: "\<And>idx ss. idx < ?n \<Longrightarrow> 0 < ss \<Longrightarrow> ss < 1 \<Longrightarrow>
      \<not>(\<exists>k<?n. edge_pt idx ss = (vx k, vy k))"
  proof -
    fix idx :: nat and ss :: real
    assume hidx: "idx < ?n" and hss1: "0 < ss" and hss2: "ss < 1"
    show "\<not>(\<exists>k<?n. edge_pt idx ss = (vx k, vy k))"
    proof
      assume "\<exists>k<?n. edge_pt idx ss = (vx k, vy k)"
      then obtain k where hk: "k < ?n"
        and hxeq_g: "(1-ss)*vx idx + ss*vx(Suc idx mod ?n) = vx k"
        and hyeq_g: "(1-ss)*vy idx + ss*vy(Suc idx mod ?n) = vy k"
        unfolding edge_pt_def by (by100 auto)
      define ag where "ag = vx idx" define bg where "bg = vx(Suc idx mod ?n)" define cg where "cg = vx k"
      define ag' where "ag' = vy idx" define bg' where "bg' = vy(Suc idx mod ?n)" define cg' where "cg' = vy k"
      have habg: "(1-ss)*ag + ss*bg = cg" using hxeq_g unfolding ag_def bg_def cg_def by (by100 simp)
      have habg': "(1-ss)*ag' + ss*bg' = cg'" using hyeq_g unfolding ag'_def bg'_def cg'_def by (by100 simp)
      have hcolx_g: "cg - ag = ss*(bg - ag)"
      proof -
        have "(1-ss)*ag = ag - ss*ag" by (by100 algebra)
        hence "ag - ss*ag + ss*bg = cg" using habg by (by100 linarith)
        hence "cg - ag = ss*bg - ss*ag" by (by100 linarith)
        thus ?thesis by (simp only: right_diff_distrib[symmetric])
      qed
      have hcoly_g: "cg' - ag' = ss*(bg' - ag')"
      proof -
        have "(1-ss)*ag' = ag' - ss*ag'" by (by100 algebra)
        hence "ag' - ss*ag' + ss*bg' = cg'" using habg' by (by100 linarith)
        hence "cg' - ag' = ss*bg' - ss*ag'" by (by100 linarith)
        thus ?thesis by (simp only: right_diff_distrib[symmetric])
      qed
      have hcross0_g: "(cg - ag)*(bg' - ag') - (cg' - ag')*(bg - ag) = 0"
        unfolding hcolx_g hcoly_g by (by100 algebra)
      have "k = idx \<or> k = Suc idx mod ?n"
      proof (rule ccontr)
        assume "\<not>(k = idx \<or> k = Suc idx mod ?n)"
        hence "k \<noteq> idx" "k \<noteq> Suc idx mod ?n" by (by100 auto)+
        from hC11 hidx hk this
        have "(vx k - vx idx)*(vy(Suc idx mod ?n) - vy idx)
            - (vy k - vy idx)*(vx(Suc idx mod ?n) - vx idx) < 0" by (by100 blast)
        hence "(cg - ag)*(bg' - ag') - (cg' - ag')*(bg - ag) < 0"
          unfolding cg_def ag_def bg'_def ag'_def cg'_def bg_def by (by100 simp)
        thus False using hcross0_g by (by100 linarith)
      qed
      thus False
      proof
        assume "k = idx" hence "cg = ag" unfolding cg_def ag_def by (by100 simp)
        hence "ss*(bg - ag) = 0" using hcolx_g by (by100 linarith)
        from this have "ss = 0 \<or> bg - ag = 0" using mult_eq_0_iff by (by100 blast)
        hence hba_g: "bg = ag" using hss1 by (by100 linarith)
        have "cg' = ag'" unfolding cg'_def ag'_def using \<open>k = idx\<close> by (by100 simp)
        hence "ss*(bg' - ag') = 0" using hcoly_g by (by100 linarith)
        from this have "ss = 0 \<or> bg' - ag' = 0" using mult_eq_0_iff by (by100 blast)
        hence "bg' = ag'" using hss1 by (by100 linarith)
        hence "(vx idx, vy idx) = (vx(Suc idx mod ?n), vy(Suc idx mod ?n))"
          using hba_g unfolding ag_def ag'_def bg_def bg'_def by (by100 simp)
        have hn_gt0_g: "?n > 0" using assms by (by100 linarith)
        have hmod_lt_g: "Suc idx mod ?n < ?n" using hn_gt0_g by (by100 simp)
        have hmod_ne_g: "idx \<noteq> Suc idx mod ?n"
        proof
          assume "idx = Suc idx mod ?n"
          hence "Suc idx mod ?n = idx mod ?n" using hidx by (by100 simp)
          hence "(Suc idx - idx) mod ?n = 0" using assms by (simp add: mod_eq_dvd_iff_nat)
          hence "?n dvd 1" by (by100 simp)
          thus False using assms by (by100 simp)
        qed
        show False using hC3 hidx hmod_lt_g hmod_ne_g
          \<open>(vx idx, vy idx) = (vx(Suc idx mod ?n), vy(Suc idx mod ?n))\<close> by (by100 blast)
      next
        assume "k = Suc idx mod ?n" hence "cg = bg" unfolding cg_def bg_def by (by100 simp)
        hence "(1-ss)*ag + ss*bg = bg" using habg by (by100 simp)
        hence "(1-ss)*ag = bg - ss*bg" by (by100 linarith)
        have "(1-ss)*bg = bg - ss*bg" by (by100 algebra)
        hence "(1-ss)*ag = (1-ss)*bg" using \<open>(1-ss)*ag = bg - ss*bg\<close> by (by100 linarith)
        hence "(1-ss)*(ag - bg) = 0"
          using right_diff_distrib[of "1-ss" ag bg] by (by100 linarith)
        have "1-ss > 0" using hss2 by (by100 linarith)
        from \<open>(1-ss)*(ag - bg) = 0\<close> have "1-ss = 0 \<or> ag - bg = 0"
          using mult_eq_0_iff by (by100 blast)
        hence hba_g: "ag = bg" using \<open>1-ss > 0\<close> by (by100 linarith)
        have "cg' = bg'" unfolding cg'_def bg'_def using \<open>k = Suc idx mod ?n\<close> by (by100 simp)
        hence "(1-ss)*ag' + ss*bg' = bg'" using habg' by (by100 simp)
        hence "(1-ss)*ag' = bg' - ss*bg'" by (by100 linarith)
        have "(1-ss)*bg' = bg' - ss*bg'" by (by100 algebra)
        hence "(1-ss)*ag' = (1-ss)*bg'" using \<open>(1-ss)*ag' = bg' - ss*bg'\<close> by (by100 linarith)
        hence "(1-ss)*(ag' - bg') = 0"
          using right_diff_distrib[of "1-ss" ag' bg'] by (by100 linarith)
        from this have "1-ss = 0 \<or> ag' - bg' = 0" using mult_eq_0_iff by (by100 blast)
        hence "ag' = bg'" using \<open>1-ss > 0\<close> by (by100 linarith)
        hence "(vx idx, vy idx) = (vx(Suc idx mod ?n), vy(Suc idx mod ?n))"
          using hba_g unfolding ag_def ag'_def bg_def bg'_def by (by100 simp)
        have hn_gt0_g: "?n > 0" using assms by (by100 linarith)
        have hmod_lt_g: "Suc idx mod ?n < ?n" using hn_gt0_g by (by100 simp)
        have hmod_ne_g: "idx \<noteq> Suc idx mod ?n"
        proof
          assume "idx = Suc idx mod ?n"
          hence "Suc idx mod ?n = idx mod ?n" using hidx by (by100 simp)
          hence "(Suc idx - idx) mod ?n = 0" using assms by (simp add: mod_eq_dvd_iff_nat)
          hence "?n dvd 1" by (by100 simp)
          thus False using assms by (by100 simp)
        qed
        show False using hC3 hidx hmod_lt_g hmod_ne_g
          \<open>(vx idx, vy idx) = (vx(Suc idx mod ?n), vy(Suc idx mod ?n))\<close> by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Helper: convex polygon edges have injective interior parameterization.
     If edge\_pt(i1,t1) = edge\_pt(i2,t2) with 0<t1,t2<1 then i1=i2 and t1=t2.\<close>
  have hedge_unique: "\<And>i1 i2 t1 t2. i1 < ?n \<Longrightarrow> i2 < ?n \<Longrightarrow> 0 < t1 \<Longrightarrow> t1 < 1 \<Longrightarrow>
      0 < t2 \<Longrightarrow> t2 < 1 \<Longrightarrow> edge_pt i1 t1 = edge_pt i2 t2 \<Longrightarrow> i1 = i2 \<and> t1 = t2"
  proof -
    fix i1 i2 :: nat and t1 t2 :: real
    assume hi1: "i1 < ?n" and hi2: "i2 < ?n"
      and ht1a: "0 < t1" and ht1b: "t1 < 1" and ht2a: "0 < t2" and ht2b: "t2 < 1"
      and heq_u: "edge_pt i1 t1 = edge_pt i2 t2"
    have heqx_u: "(1-t1)*vx i1 + t1*vx(Suc i1 mod ?n) = (1-t2)*vx i2 + t2*vx(Suc i2 mod ?n)"
      using heq_u unfolding edge_pt_def by (by100 simp)
    have heqy_u: "(1-t1)*vy i1 + t1*vy(Suc i1 mod ?n) = (1-t2)*vy i2 + t2*vy(Suc i2 mod ?n)"
      using heq_u unfolding edge_pt_def by (by100 simp)
    show "i1 = i2 \<and> t1 = t2"
    proof (cases "i1 = i2")
      case True
      \<comment> \<open>Same edge: (t1-t2)*(endpoint - startpoint) = 0 in both coords.
         Since vertices are distinct (C3), t1 = t2.\<close>
      have ht_eq: "t1 = t2"
      proof -
        from heqx_u True
        have "(1-t1)*vx i1 + t1*vx(Suc i1 mod ?n) = (1-t2)*vx i1 + t2*vx(Suc i1 mod ?n)"
          by (by100 simp)
        hence hx0: "(t1-t2)*(vx(Suc i1 mod ?n) - vx i1) = 0" by (by100 algebra)
        from heqy_u True
        have "(1-t1)*vy i1 + t1*vy(Suc i1 mod ?n) = (1-t2)*vy i1 + t2*vy(Suc i1 mod ?n)"
          by (by100 simp)
        hence hy0: "(t1-t2)*(vy(Suc i1 mod ?n) - vy i1) = 0" by (by100 algebra)
        have hn_gt0_u: "?n > 0" using assms by (by100 linarith)
        have hmod_lt_u: "Suc i1 mod ?n < ?n" using hn_gt0_u by (by100 simp)
        have hmod_ne_u: "i1 \<noteq> Suc i1 mod ?n"
        proof
          assume "i1 = Suc i1 mod ?n"
          hence "Suc i1 mod ?n = i1 mod ?n" using hi1 by (by100 simp)
          hence "(Suc i1 - i1) mod ?n = 0" using assms by (simp add: mod_eq_dvd_iff_nat)
          hence "?n dvd 1" by (by100 simp)
          thus False using assms by (by100 simp)
        qed
        have "(vx i1, vy i1) \<noteq> (vx(Suc i1 mod ?n), vy(Suc i1 mod ?n))"
          using hC3 hi1 hmod_lt_u hmod_ne_u by (by100 blast)
        hence "vx i1 \<noteq> vx(Suc i1 mod ?n) \<or> vy i1 \<noteq> vy(Suc i1 mod ?n)" by (by100 auto)
        thus "t1 = t2"
        proof
          assume "vx i1 \<noteq> vx(Suc i1 mod ?n)"
          hence "vx(Suc i1 mod ?n) - vx i1 \<noteq> 0" by (by100 linarith)
          from hx0 this show "t1 = t2"
            using mult_eq_0_iff[of "t1 - t2" "vx(Suc i1 mod ?n) - vx i1"] by (by100 linarith)
        next
          assume "vy i1 \<noteq> vy(Suc i1 mod ?n)"
          hence "vy(Suc i1 mod ?n) - vy i1 \<noteq> 0" by (by100 linarith)
          from hy0 this show "t1 = t2"
            using mult_eq_0_iff[of "t1 - t2" "vy(Suc i1 mod ?n) - vy i1"] by (by100 linarith)
        qed
      qed
      thus ?thesis using True by (by100 simp)
    next
      case hne_u: False
      \<comment> \<open>Different edges: cross product argument gives contradiction.
         Key idea: the point lies on edge i1 (cross with edge direction = 0)
         but C11 forces all non-endpoint vertices to have cross < 0.\<close>
      define dx_u where "dx_u = vx(Suc i1 mod ?n) - vx i1"
      define dy_u where "dy_u = vy(Suc i1 mod ?n) - vy i1"
      have hn_gt0_u: "?n > 0" using assms by (by100 linarith)
      have hi1s_lt: "Suc i1 mod ?n < ?n" using hn_gt0_u by (by100 simp)
      have hi2s_lt: "Suc i2 mod ?n < ?n" using hn_gt0_u by (by100 simp)
      \<comment> \<open>From edge i1: point = (1-t1)*v\_i1 + t1*v\_{Suc i1}.
         Translated: point - v\_i1 = t1*(v\_{Suc i1} - v\_i1) = t1*(dx\_u, dy\_u).\<close>
      have px_u: "(1-t2)*(vx i2 - vx i1) + t2*(vx(Suc i2 mod ?n) - vx i1) = t1 * dx_u"
      proof -
        have "(1-t2)*(vx i2 - vx i1) + t2*(vx(Suc i2 mod ?n) - vx i1)
            = (1-t2)*vx i2 + t2*vx(Suc i2 mod ?n) - vx i1" by (by100 algebra)
        also have "\<dots> = (1-t1)*vx i1 + t1*vx(Suc i1 mod ?n) - vx i1"
          using heqx_u by (by100 linarith)
        also have "\<dots> = t1*(vx(Suc i1 mod ?n) - vx i1)" by (by100 algebra)
        finally show ?thesis unfolding dx_u_def by (by100 simp)
      qed
      have py_u: "(1-t2)*(vy i2 - vy i1) + t2*(vy(Suc i2 mod ?n) - vy i1) = t1 * dy_u"
      proof -
        have "(1-t2)*(vy i2 - vy i1) + t2*(vy(Suc i2 mod ?n) - vy i1)
            = (1-t2)*vy i2 + t2*vy(Suc i2 mod ?n) - vy i1" by (by100 algebra)
        also have "\<dots> = (1-t1)*vy i1 + t1*vy(Suc i1 mod ?n) - vy i1"
          using heqy_u by (by100 linarith)
        also have "\<dots> = t1*(vy(Suc i1 mod ?n) - vy i1)" by (by100 algebra)
        finally show ?thesis unfolding dy_u_def by (by100 simp)
      qed
      \<comment> \<open>Cross product of translated point with edge direction = 0.\<close>
      have cross0_u: "((1-t2)*(vx i2 - vx i1) + t2*(vx(Suc i2 mod ?n) - vx i1))*dy_u
         - ((1-t2)*(vy i2 - vy i1) + t2*(vy(Suc i2 mod ?n) - vy i1))*dx_u = 0"
        using px_u py_u by (by100 algebra)
      \<comment> \<open>Expand cross as convex combination of individual vertex crosses.\<close>
      have expand_u: "((1-t2)*(vx i2 - vx i1) + t2*(vx(Suc i2 mod ?n) - vx i1))*dy_u
         - ((1-t2)*(vy i2 - vy i1) + t2*(vy(Suc i2 mod ?n) - vy i1))*dx_u
         = (1-t2)*((vx i2 - vx i1)*dy_u - (vy i2 - vy i1)*dx_u)
         + t2*((vx(Suc i2 mod ?n) - vx i1)*dy_u - (vy(Suc i2 mod ?n) - vy i1)*dx_u)"
        by (by100 algebra)
      \<comment> \<open>Define the two cross terms for readability.\<close>
      define A_u where "A_u = (vx i2 - vx i1)*dy_u - (vy i2 - vy i1)*dx_u"
      define B_u where "B_u = (vx(Suc i2 mod ?n) - vx i1)*dy_u - (vy(Suc i2 mod ?n) - vy i1)*dx_u"
      \<comment> \<open>A\_u \<le> 0: C11 gives < 0 unless i2 = Suc i1 mod n (where cross = 0).\<close>
      have hAle: "A_u \<le> 0"
      proof (cases "i2 = Suc i1 mod ?n")
        case True
        hence "A_u = dx_u*dy_u - dy_u*dx_u" unfolding A_u_def dx_u_def dy_u_def by (by100 simp)
        thus ?thesis by (by100 simp)
      next
        case False
        from hC11 hi1 hi2 hne_u False
        have "(vx i2 - vx i1)*(vy(Suc i1 mod ?n) - vy i1)
            - (vy i2 - vy i1)*(vx(Suc i1 mod ?n) - vx i1) < 0" by (by100 blast)
        thus ?thesis unfolding A_u_def dx_u_def dy_u_def by (by100 linarith)
      qed
      \<comment> \<open>B\_u \<le> 0: similarly, C11 gives < 0 unless Suc i2 mod n \<in> {i1, Suc i1 mod n}.\<close>
      have hBle: "B_u \<le> 0"
      proof (cases "Suc i2 mod ?n = i1 \<or> Suc i2 mod ?n = Suc i1 mod ?n")
        case True
        hence "B_u = 0"
        proof
          assume "Suc i2 mod ?n = i1"
          thus ?thesis unfolding B_u_def by (by100 simp)
        next
          assume "Suc i2 mod ?n = Suc i1 mod ?n"
          thus ?thesis unfolding B_u_def dx_u_def dy_u_def by (by100 simp)
        qed
        thus ?thesis by (by100 linarith)
      next
        case False
        hence "Suc i2 mod ?n \<noteq> i1" "Suc i2 mod ?n \<noteq> Suc i1 mod ?n" by (by100 auto)+
        from hC11 hi1 hi2s_lt this
        have "(vx(Suc i2 mod ?n) - vx i1)*(vy(Suc i1 mod ?n) - vy i1)
            - (vy(Suc i2 mod ?n) - vy i1)*(vx(Suc i1 mod ?n) - vx i1) < 0" by (by100 blast)
        thus ?thesis unfolding B_u_def dx_u_def dy_u_def by (by100 linarith)
      qed
      \<comment> \<open>From convex combination = 0 with both terms \<le> 0: both must be 0.\<close>
      have hconv_u: "(1-t2)*A_u + t2*B_u = 0"
        using cross0_u expand_u unfolding A_u_def B_u_def by (by100 linarith)
      have h1t2: "1-t2 > 0" using ht2b by (by100 linarith)
      have ht2p: "t2 > 0" using ht2a .
      have "(1-t2)*A_u \<le> 0"
        using h1t2 hAle mult_nonneg_nonpos[of "1-t2" A_u] by (by100 linarith)
      have "t2*B_u \<le> 0"
        using ht2p hBle mult_nonneg_nonpos[of t2 B_u] by (by100 linarith)
      have h1tA0: "(1-t2)*A_u = 0"
        using \<open>(1-t2)*A_u \<le> 0\<close> \<open>t2*B_u \<le> 0\<close> hconv_u by (by100 linarith)
      have hA0: "A_u = 0"
      proof -
        from h1tA0 have "1-t2 = 0 \<or> A_u = 0"
          using mult_eq_0_iff by (by100 blast)
        thus ?thesis using h1t2 by (by100 linarith)
      qed
      have hB0: "B_u = 0"
      proof -
        have "t2*B_u = 0" using h1tA0 hconv_u by (by100 linarith)
        from this have "t2 = 0 \<or> B_u = 0" using mult_eq_0_iff by (by100 blast)
        thus ?thesis using ht2p by (by100 linarith)
      qed
      \<comment> \<open>From A\_u = 0 and i1 \<noteq> i2: must have i2 = Suc i1 mod n.\<close>
      have hi2eq: "i2 = Suc i1 mod ?n"
      proof (rule ccontr)
        assume "i2 \<noteq> Suc i1 mod ?n"
        from hC11 hi1 hi2 hne_u this
        have "(vx i2 - vx i1)*(vy(Suc i1 mod ?n) - vy i1)
            - (vy i2 - vy i1)*(vx(Suc i1 mod ?n) - vx i1) < 0" by (by100 blast)
        hence "A_u < 0" unfolding A_u_def dx_u_def dy_u_def by (by100 linarith)
        thus False using hA0 by (by100 linarith)
      qed
      \<comment> \<open>From B\_u = 0: Suc i2 mod n must be i1 (only other zero option Suc i1 mod n
         would give i2 = i1 by the Suc-mod injectivity below).\<close>
      have hsi2eq: "Suc i2 mod ?n = i1"
      proof (rule ccontr)
        assume hne2: "Suc i2 mod ?n \<noteq> i1"
        have "Suc i2 mod ?n \<noteq> Suc i1 mod ?n"
        proof
          assume heq_s: "Suc i2 mod ?n = Suc i1 mod ?n"
          \<comment> \<open>Suc i2 mod n = Suc i1 mod n with i1,i2 < n implies i2 = i1.\<close>
          have "Suc i2 \<le> ?n" using hi2 by (by100 linarith)
          have "Suc i1 \<le> ?n" using hi1 by (by100 linarith)
          have "i2 = i1"
          proof (cases "Suc i2 < ?n")
            case True hence "Suc i2 mod ?n = Suc i2" by (by100 simp)
            show ?thesis
            proof (cases "Suc i1 < ?n")
              case True2: True hence "Suc i1 mod ?n = Suc i1" by (by100 simp)
              from heq_s \<open>Suc i2 mod ?n = Suc i2\<close> True2 show ?thesis by (by100 simp)
            next
              case False hence "Suc i1 = ?n" using \<open>Suc i1 \<le> ?n\<close> by (by100 linarith)
              hence "Suc i1 mod ?n = 0" by (by100 simp)
              from heq_s \<open>Suc i2 mod ?n = Suc i2\<close> this have "Suc i2 = 0" by (by100 simp)
              thus ?thesis by (by100 simp)
            qed
          next
            case False hence "Suc i2 = ?n" using \<open>Suc i2 \<le> ?n\<close> by (by100 linarith)
            hence "Suc i2 mod ?n = 0" by (by100 simp)
            show ?thesis
            proof (cases "Suc i1 < ?n")
              case True hence "Suc i1 mod ?n = Suc i1" by (by100 simp)
              from heq_s \<open>Suc i2 mod ?n = 0\<close> this have "Suc i1 = 0" by (by100 simp)
              thus ?thesis by (by100 simp)
            next
              case False hence "Suc i1 = ?n" using \<open>Suc i1 \<le> ?n\<close> by (by100 linarith)
              from \<open>Suc i2 = ?n\<close> this show ?thesis by (by100 simp)
            qed
          qed
          thus False using hne_u by (by100 simp)
        qed
        from hC11 hi1 hi2s_lt hne2 this
        have "(vx(Suc i2 mod ?n) - vx i1)*(vy(Suc i1 mod ?n) - vy i1)
            - (vy(Suc i2 mod ?n) - vy i1)*(vx(Suc i1 mod ?n) - vx i1) < 0" by (by100 blast)
        hence "B_u < 0" unfolding B_u_def dx_u_def dy_u_def by (by100 linarith)
        thus False using hB0 by (by100 linarith)
      qed
      \<comment> \<open>Now i2 = Suc i1 mod n and Suc i2 mod n = i1.
         This means Suc(Suc i1 mod n) mod n = i1, giving n | 2.
         Since n \<ge> 3, contradiction.\<close>
      have "Suc (Suc i1 mod ?n) mod ?n = i1"
        using hi2eq hsi2eq by (by100 simp)
      have False
      proof (cases "Suc i1 < ?n")
        case True hence "Suc i1 mod ?n = Suc i1" by (by100 simp)
        hence "Suc (Suc i1) mod ?n = i1" using \<open>Suc (Suc i1 mod ?n) mod ?n = i1\<close> by (by100 simp)
        show False
        proof (cases "Suc (Suc i1) < ?n")
          case True2: True hence "Suc (Suc i1) mod ?n = Suc (Suc i1)" by (by100 simp)
          from \<open>Suc (Suc i1) mod ?n = i1\<close> this have "Suc (Suc i1) = i1" by (by100 simp)
          thus False by (by100 simp)
        next
          case False hence "Suc (Suc i1) \<ge> ?n" by (by100 linarith)
          moreover have "Suc (Suc i1) \<le> Suc ?n" using True by (by100 linarith)
          ultimately have "Suc (Suc i1) = ?n \<or> Suc (Suc i1) = Suc ?n" by (by100 linarith)
          thus False
          proof
            assume "Suc (Suc i1) = ?n"
            hence "Suc (Suc i1) mod ?n = 0" by (by100 simp)
            from \<open>Suc (Suc i1) mod ?n = i1\<close> this have "i1 = 0" by (by100 simp)
            hence "?n = 2" using \<open>Suc (Suc i1) = ?n\<close> by (by100 simp)
            thus False using assms by (by100 linarith)
          next
            assume "Suc (Suc i1) = Suc ?n"
            hence "Suc i1 = ?n" by (by100 simp)
            thus False using True by (by100 linarith)
          qed
        qed
      next
        case False hence "Suc i1 = ?n" using hi1 by (by100 linarith)
        hence "Suc i1 mod ?n = 0" by (by100 simp)
        hence "Suc 0 mod ?n = i1" using \<open>Suc (Suc i1 mod ?n) mod ?n = i1\<close> by (by100 simp)
        have "1 mod ?n = (1::nat)" using assms by (by100 simp)
        hence "i1 = 1" using \<open>Suc 0 mod ?n = i1\<close> by (by100 simp)
        hence "?n = 2" using \<open>Suc i1 = ?n\<close> by (by100 simp)
        thus False using assms by (by100 linarith)
      qed
      thus ?thesis by (by100 simp)
    qed
  qed
  \<comment> \<open>C2 (quotient map): q is continuous, surjective, TY is quotient topology.\<close>
  have hC2: "top1_quotient_map_on P
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q"
  proof -
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    have htopo_P_c2: "is_topology_on P ?TP"
    proof -
      have "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
        by (by100 simp)
      thus ?thesis by (rule subspace_topology_is_topology_on) (by100 simp)
    qed
    have htopo_Y_c2: "is_topology_on Y TY"
    proof -
      \<comment> \<open>TY equals the standard quotient topology by map. Show equivalence.\<close>
      have hTY_eq: "TY = top1_quotient_topology_by_map_on P ?TP Y q"
      proof (intro equalityI subsetI)
        fix U assume "U \<in> TY"
        then obtain W where hW: "W \<subseteq> P" "\<forall>x\<in>W. \<forall>y. y\<in>P \<and> q y = q x \<longrightarrow> y \<in> W"
          "U = q ` W" "W \<in> ?TP" unfolding TY_def by (by100 blast)
        have "U \<subseteq> Y" using hW(3) unfolding Y_def using hW(1) by (by100 blast)
        have "{x\<in>P. q x \<in> U} = W"
        proof (intro equalityI subsetI)
          fix x assume "x \<in> {x\<in>P. q x \<in> U}"
          hence "x \<in> P" "q x \<in> q ` W" using hW(3) by (by100 auto)+
          then obtain w where "w \<in> W" "q x = q w" by (by100 blast)
          thus "x \<in> W" using hW(2) \<open>x \<in> P\<close> hW(1) by (by100 blast)
        next
          fix x assume "x \<in> W" thus "x \<in> {x\<in>P. q x \<in> U}" using hW(1) hW(3) by (by100 blast)
        qed
        hence "{x\<in>P. q x \<in> U} \<in> ?TP" using hW(4) by (by100 simp)
        thus "U \<in> top1_quotient_topology_by_map_on P ?TP Y q"
          unfolding top1_quotient_topology_by_map_on_def using \<open>U \<subseteq> Y\<close> by (by100 blast)
      next
        fix U assume "U \<in> top1_quotient_topology_by_map_on P ?TP Y q"
        hence hU: "U \<subseteq> Y" "{x\<in>P. q x \<in> U} \<in> ?TP"
          unfolding top1_quotient_topology_by_map_on_def by (by100 blast)+
        define W where "W = {x\<in>P. q x \<in> U}"
        have "W \<subseteq> P" unfolding W_def by (by100 blast)
        have "\<forall>x\<in>W. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> W" unfolding W_def by (by100 auto)
        have "U = q ` W"
        proof (intro equalityI subsetI)
          fix u assume "u \<in> U"
          hence "u \<in> Y" using hU(1) by (by100 blast)
          then obtain x where "x \<in> P" "q x = u" unfolding Y_def by (by100 blast)
          hence "x \<in> W" unfolding W_def using \<open>u \<in> U\<close> by (by100 blast)
          thus "u \<in> q ` W" using \<open>q x = u\<close> by (by100 blast)
        next
          fix u assume "u \<in> q ` W" thus "u \<in> U" unfolding W_def by (by100 blast)
        qed
        have "W \<in> ?TP" using hU(2) unfolding W_def .
        show "U \<in> TY" unfolding TY_def
          using \<open>W \<subseteq> P\<close> \<open>\<forall>x\<in>W. _\<close> \<open>U = q ` W\<close> \<open>W \<in> ?TP\<close> by (by100 blast)
      qed
      have hpmap: "\<forall>x\<in>P. q x \<in> Y" unfolding Y_def by (by100 blast)
      from top1_quotient_topology_by_map_on_is_topology_on[OF htopo_P_c2 hpmap]
      show ?thesis using hTY_eq by (by100 simp)
    qed
    show ?thesis unfolding top1_quotient_map_on_def
    proof (intro conjI)
      show "is_topology_on P ?TP" using htopo_P_c2 .
      show "is_topology_on Y TY" using htopo_Y_c2 .
      \<comment> \<open>q continuous: preimage of open is open. By quotient topology definition.\<close>
      show "top1_continuous_map_on P ?TP Y TY q"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> P" thus "q x \<in> Y" unfolding Y_def by (by100 blast)
      next
        fix V assume hV: "V \<in> TY"
        from hV obtain W where hW_sub: "W \<subseteq> P"
          and hW_sat: "\<forall>x\<in>W. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> W"
          and hV_eq: "V = q ` W" and hW_open: "W \<in> ?TP"
          unfolding TY_def by (by100 blast)
        have "{x \<in> P. q x \<in> V} = W"
        proof (intro equalityI subsetI)
          fix x assume "x \<in> {x \<in> P. q x \<in> V}"
          hence "x \<in> P" "q x \<in> q ` W" using hV_eq by (by100 auto)+
          then obtain w where "w \<in> W" "q x = q w" by (by100 blast)
          thus "x \<in> W" using hW_sat \<open>x \<in> P\<close> hW_sub by (by100 blast)
        next
          fix x assume "x \<in> W"
          hence "x \<in> P" using hW_sub by (by100 blast)
          moreover have "q x \<in> V" using \<open>x \<in> W\<close> hV_eq by (by100 blast)
          ultimately show "x \<in> {x \<in> P. q x \<in> V}" by (by100 blast)
        qed
        thus "{x \<in> P. q x \<in> V} \<in> ?TP" using hW_open by (by100 simp)
      qed
      show "q ` P = Y" unfolding Y_def by (by100 simp)
      \<comment> \<open>Quotient condition: saturated open preimage gives open set.\<close>
      show "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x \<in> P. q x \<in> V} \<in> ?TP \<longrightarrow> V \<in> TY)"
      proof (intro allI impI)
        fix V assume hVsub: "V \<subseteq> Y" and hpre: "{x \<in> P. q x \<in> V} \<in> ?TP"
        define W where "W = {x \<in> P. q x \<in> V}"
        have "W \<subseteq> P" unfolding W_def by (by100 blast)
        have "\<forall>x\<in>W. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> W" unfolding W_def by (by100 auto)
        have "V = q ` W"
        proof (intro equalityI subsetI)
          fix v assume "v \<in> V"
          hence "v \<in> Y" using hVsub by (by100 blast)
          hence "\<exists>x \<in> P. q x = v" unfolding Y_def by (by100 blast)
          then obtain x where "x \<in> P" "q x = v" by (by100 blast)
          hence "x \<in> W" unfolding W_def using \<open>v \<in> V\<close> by (by100 blast)
          thus "v \<in> q ` W" using \<open>q x = v\<close> by (by100 blast)
        next
          fix v assume "v \<in> q ` W"
          then obtain x where "x \<in> W" "q x = v" by (by100 blast)
          thus "v \<in> V" unfolding W_def by (by100 blast)
        qed
        have "W \<in> ?TP" using hpre unfolding W_def .
        show "V \<in> TY" unfolding TY_def
          using \<open>W \<subseteq> P\<close> \<open>\<forall>x\<in>W. _\<close> \<open>V = q ` W\<close> \<open>W \<in> ?TP\<close> by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>C7/C8: Edge identification pattern matches the scheme.\<close>
  have hC8: "\<forall>i<?n. \<forall>j<?n. fst(scheme!i) = fst(scheme!j) \<longrightarrow>
      (\<forall>t\<in>I_set.
         q ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))
       = (if snd(scheme!i) = snd(scheme!j)
          then q ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))
          else q (t*vx j + (1-t)*vx(Suc j mod ?n), t*vy j + (1-t)*vy(Suc j mod ?n))))"
  proof (intro allI impI ballI)
    fix i j t assume hi: "i < ?n" and hj: "j < ?n" and hlabel: "fst(scheme!i) = fst(scheme!j)"
      and ht: "t \<in> I_set"
    \<comment> \<open>Need: q(edge\\_pt i t) = (if same\\_dir then q(edge\\_pt j t) else q(edge\\_pt j (1-t))).\<close>
    show "q ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))
       = (if snd(scheme!i) = snd(scheme!j)
          then q ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))
          else q (t*vx j + (1-t)*vx(Suc j mod ?n), t*vy j + (1-t)*vy(Suc j mod ?n)))"
    proof (cases "i = j")
      case True thus ?thesis by (by100 simp)
    next
      case hij: False
      have hpi: "partner i = j" using partner_unique[OF hi hj hij hlabel] .
      have hpj: "partner j = i" using partner_unique[OF hj hi hij[symmetric] hlabel[symmetric]] .
      have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
      \<comment> \<open>Case split on whether t is a vertex (0 or 1) or interior.\<close>
      show ?thesis
      proof (cases "0 < t \<and> t < 1")
        case hint: True \<comment> \<open>Edge interior: q enters the edge-interior branch.\<close>
        \<comment> \<open>hnotvertex_gen and hedge_unique are available from top-level scope.\<close>
        \<comment> \<open>Instantiate for edge i at parameter t.\<close>
        have hnotvertex_i: "\<not>(\<exists>k<?n. (1-t)*vx i + t*vx(Suc i mod ?n) = vx k \<and> (1-t)*vy i + t*vy(Suc i mod ?n) = vy k)"
        proof -
          have "0 < t" "t < 1" using hint by (by100 auto)+
          from hnotvertex_gen[OF hi this] show ?thesis unfolding edge_pt_def by (by100 auto)
        qed
        \<comment> \<open>For the interior case: q on canonical edges = id, q on non-canonical = partner.
           Both sides evaluate to the same canonical edge point.\<close>
        \<comment> \<open>Rewrite goal in terms of edge\\_pt.\<close>
        have hgoal_lhs: "edge_pt i t = ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))"
          unfolding edge_pt_def by (by100 simp)
        show ?thesis
        proof (cases "is_canonical i")
          case hican: True \<comment> \<open>i canonical, j non-canonical.\<close>
          hence hjnon: "\<not> is_canonical j"
          proof -
            have "i \<le> partner i" using hican unfolding is_canonical_def by (by100 simp)
            hence "i \<le> j" using hpi by (by100 simp)
            hence "i < j" using hij by (by100 linarith)
            hence "j > partner j" using hpj by (by100 simp)
            thus ?thesis unfolding is_canonical_def by (by100 linarith)
          qed
          \<comment> \<open>q(edge\\_pt i t) = edge\\_pt(i,t) since i canonical and not a vertex.\<close>
          have hqi: "q (edge_pt i t) = edge_pt i t"
          proof -
            \<comment> \<open>Not a vertex.\<close>
            have hv: "\<not>(\<exists>k<?n. edge_pt i t = (vx k, vy k))"
              using hnotvertex_i unfolding edge_pt_def by (by100 simp)
            \<comment> \<open>Not on any non-canonical edge interior.\<close>
            have he: "\<not>(\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i')"
            proof
              assume "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i'"
              then obtain i' t' where hi': "i' < ?n" "0 < t'" "t' < 1" "edge_pt i t = edge_pt i' t'" "\<not> is_canonical i'"
                by (by100 blast)
              \<comment> \<open>Edges i and i' share interior point. By C6 + adjacency: i = i'.\<close>
              have "i = i'"
              proof -
                have "0 < t" "t < 1" using hint by (by100 auto)+
                from hedge_unique[OF hi hi'(1) this hi'(2) hi'(3) hi'(4)]
                show ?thesis by (by100 simp)
              qed
              thus False using hican hi'(5) by (by100 simp)
            qed
            show ?thesis unfolding q_def using hv he by (by100 auto)
          qed
          \<comment> \<open>q(edge\\_pt j s) where s is the matching param.\<close>
          have hqj: "\<And>s. 0 < s \<Longrightarrow> s < 1 \<Longrightarrow> q (edge_pt j s) = edge_pt i
              (if snd(scheme!j) = snd(scheme!i) then s else 1 - s)"
          proof -
            fix s :: real assume hs: "0 < s" "s < 1"
            \<comment> \<open>edge\\_pt(j,s) is not a vertex.\<close>
            have hvj: "\<not>(\<exists>k<?n. edge_pt j s = (vx k, vy k))"
              using hnotvertex_gen[OF hj hs(1) hs(2)] .
            \<comment> \<open>edge\\_pt(j,s) IS on non-canonical edge j.\<close>
            have hexj: "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i'"
              using hj hs hjnon by (by100 blast)
            \<comment> \<open>q enters edge-interior branch. SOME picks (j', s'). By uniqueness j' = j, s' = s.\<close>
            define sel where "sel = (SOME (i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i')"
            define j' where "j' = fst sel" define s' where "s' = snd sel"
            have hsel: "j' < ?n \<and> 0 < s' \<and> s' < 1 \<and> edge_pt j s = edge_pt j' s' \<and> \<not> is_canonical j'"
            proof -
              from hexj have "\<exists>p. (\<lambda>(i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i') p"
                by (by100 auto)
              from someI_ex[OF this] show ?thesis unfolding sel_def j'_def s'_def by (by100 auto)
            qed
            \<comment> \<open>By edge uniqueness: j' = j and s' = s.\<close>
            have "j' = j \<and> s' = s"
            proof -
              from hsel have hj'_lt: "j' < ?n" and hs'a: "0 < s'" and hs'b: "s' < 1"
                and heq_js: "edge_pt j s = edge_pt j' s'" by (by100 auto)+
              from hedge_unique[OF hj hj'_lt hs(1) hs(2) hs'a hs'b heq_js]
              show ?thesis by (by100 simp)
            qed
            hence "partner j' = partner j" and "snd(scheme!j') = snd(scheme!j)" by (by100 auto)+
            hence "q (edge_pt j s) = edge_pt (partner j) (if snd(scheme!j) = snd(scheme!(partner j)) then s else 1-s)"
            proof -
              have "q (edge_pt j s) = (let (i',t') = sel in let jj = partner i' in
                  if snd(scheme!i') = snd(scheme!jj) then edge_pt jj t' else edge_pt jj (1-t'))"
                unfolding q_def sel_def using hexj hvj by (by100 auto)
              also have "\<dots> = (let jj = partner j' in
                  if snd(scheme!j') = snd(scheme!jj) then edge_pt jj s' else edge_pt jj (1-s'))"
              proof -
                have "sel = (j', s')" unfolding j'_def s'_def by (by100 simp)
                thus ?thesis by (by100 simp)
              qed
              also have "\<dots> = (if snd(scheme!j) = snd(scheme!(partner j)) then edge_pt (partner j) s else edge_pt (partner j) (1-s))"
                using \<open>j' = j \<and> s' = s\<close> by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            thus "q (edge_pt j s) = edge_pt i (if snd(scheme!j) = snd(scheme!i) then s else 1 - s)"
              using hpj by (by100 simp)
          qed
          show ?thesis
          proof (cases "snd(scheme!i) = snd(scheme!j)")
            case True \<comment> \<open>Same direction.\<close>
            have "q (edge_pt j t) = edge_pt i t" using hqj hint True by (by100 simp)
            thus ?thesis using hqi hgoal_lhs True unfolding edge_pt_def by (by100 simp)
          next
            case False \<comment> \<open>Opposite direction.\<close>
            have "0 < 1 - t" "1 - t < 1" using hint by (by100 linarith)+
            hence "q (edge_pt j (1-t)) = edge_pt i (1 - (1-t))"
              using hqj[of "1-t"] False by (by100 simp)
            hence "q (edge_pt j (1-t)) = edge_pt i t" by (by100 simp)
            thus ?thesis using hqi hgoal_lhs False unfolding edge_pt_def by (by100 simp)
          qed
        next
          case hican: False \<comment> \<open>i non-canonical, j canonical. Symmetric to the True case.\<close>
          hence hjcan: "is_canonical j"
          proof -
            have "\<not>(i \<le> partner i)" using hican unfolding is_canonical_def by (by100 simp)
            hence "i > partner i" by (by100 linarith)
            hence "i > j" using hpi by (by100 simp)
            hence "j < i" by (by100 linarith)
            hence "j \<le> partner j" using hpj by (by100 simp)
            thus ?thesis unfolding is_canonical_def by (by100 simp)
          qed
          \<comment> \<open>q(edge\\_pt i t): i non-canonical, so q enters edge-interior branch.\<close>
          have hqi_nc: "q (edge_pt i t) = edge_pt j (if snd(scheme!i) = snd(scheme!j) then t else 1-t)"
          proof -
            have ht_pos: "0 < t" and ht_lt1: "t < 1" using hint by (by100 auto)+
            have hv_i: "\<not>(\<exists>k<?n. edge_pt i t = (vx k, vy k))"
              using hnotvertex_gen[OF hi ht_pos ht_lt1] .
            have hex_i: "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i'"
              using hi ht_pos ht_lt1 hican by (by100 blast)
            define sel_i where "sel_i = (SOME (i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i')"
            define i'' where "i'' = fst sel_i" define t'' where "t'' = snd sel_i"
            have hsel_i: "i'' < ?n \<and> 0 < t'' \<and> t'' < 1 \<and> edge_pt i t = edge_pt i'' t'' \<and> \<not> is_canonical i''"
            proof -
              from hex_i have "\<exists>p. (\<lambda>(i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i') p"
                by (by100 auto)
              from someI_ex[OF this] show ?thesis unfolding sel_i_def i''_def t''_def by (by100 auto)
            qed
            have hii: "i'' = i \<and> t'' = t"
            proof -
              from hsel_i have "i'' < ?n" "0 < t''" "t'' < 1" "edge_pt i t = edge_pt i'' t''"
                by (by100 auto)+
              from hedge_unique[OF hi this(1) ht_pos ht_lt1 this(2) this(3) this(4)]
              show ?thesis by (by100 simp)
            qed
            have "q (edge_pt i t) = (let (i',t') = sel_i in let jj = partner i' in
                if snd(scheme!i') = snd(scheme!jj) then edge_pt jj t' else edge_pt jj (1-t'))"
              unfolding q_def sel_i_def using hex_i hv_i by (by100 auto)
            also have "\<dots> = (let jj = partner i'' in
                if snd(scheme!i'') = snd(scheme!jj) then edge_pt jj t'' else edge_pt jj (1-t''))"
            proof -
              have "sel_i = (i'', t'')" unfolding i''_def t''_def by (by100 simp)
              thus ?thesis by (by100 simp)
            qed
            also have "\<dots> = (if snd(scheme!i) = snd(scheme!(partner i)) then edge_pt (partner i) t else edge_pt (partner i) (1-t))"
              using hii by (by100 simp)
            finally show ?thesis using hpi by (by100 simp)
          qed
          \<comment> \<open>q(edge\\_pt j s): j canonical, so q enters else branch (identity).\<close>
          have hqj_c: "\<And>s. 0 < s \<Longrightarrow> s < 1 \<Longrightarrow> q (edge_pt j s) = edge_pt j s"
          proof -
            fix s :: real assume hs_c: "0 < s" "s < 1"
            have hv_j: "\<not>(\<exists>k<?n. edge_pt j s = (vx k, vy k))"
              using hnotvertex_gen[OF hj hs_c(1) hs_c(2)] .
            have he_j: "\<not>(\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i')"
            proof
              assume "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i'"
              then obtain i' t' where hi': "i' < ?n" "0 < t'" "t' < 1" "edge_pt j s = edge_pt i' t'" "\<not> is_canonical i'"
                by (by100 blast)
              have "j = i'"
              proof -
                from hedge_unique[OF hj hi'(1) hs_c(1) hs_c(2) hi'(2) hi'(3) hi'(4)]
                show ?thesis by (by100 simp)
              qed
              thus False using hjcan hi'(5) by (by100 simp)
            qed
            show "q (edge_pt j s) = edge_pt j s" unfolding q_def using hv_j he_j by (by100 auto)
          qed
          \<comment> \<open>Combine: same direction or opposite.\<close>
          show ?thesis
          proof (cases "snd(scheme!i) = snd(scheme!j)")
            case True \<comment> \<open>Same direction.\<close>
            have "0 < t" "t < 1" using hint by (by100 auto)+
            have "q (edge_pt i t) = edge_pt j t" using hqi_nc True by (by100 simp)
            moreover have "q (edge_pt j t) = edge_pt j t" using hqj_c \<open>0 < t\<close> \<open>t < 1\<close> by (by100 simp)
            ultimately have "q (edge_pt i t) = q (edge_pt j t)" by (by100 simp)
            thus ?thesis using hgoal_lhs True unfolding edge_pt_def by (by100 simp)
          next
            case False \<comment> \<open>Opposite direction.\<close>
            have "0 < t" "t < 1" using hint by (by100 auto)+
            have "0 < 1-t" "1-t < 1" using \<open>0 < t\<close> \<open>t < 1\<close> by (by100 linarith)+
            have "q (edge_pt i t) = edge_pt j (1-t)" using hqi_nc False by (by100 simp)
            moreover have "q (edge_pt j (1-t)) = edge_pt j (1-t)"
              using hqj_c \<open>0 < 1-t\<close> \<open>1-t < 1\<close> by (by100 simp)
            ultimately have "q (edge_pt i t) = q (edge_pt j (1-t))" by (by100 simp)
            thus ?thesis using hgoal_lhs False unfolding edge_pt_def by (by100 simp)
          qed
        qed
      next
        case hvert: False \<comment> \<open>Vertex: t = 0 or t = 1. q enters the vertex branch.\<close>
        hence "t = 0 \<or> t = 1" using ht01 by (by100 linarith)
        \<comment> \<open>Vertex case: t=0 gives v\\_i, t=1 gives v\\_{Suc i mod n}.
           The vtx\\_id relation captures the vertex identifications from each edge pairing.
           vtgt\\_class ensures vertices in the same equivalence class map to the same rep.\<close>
        thus ?thesis
        proof
          assume ht0: "t = 0"
          \<comment> \<open>LHS: q(v\\_i) = (vx(vtgt i), vy(vtgt i)). RHS depends on direction.\<close>
          have hq_vi: "q (edge_pt i 0) = (vx (vtgt i), vy (vtgt i))"
          proof -
            have hvi: "edge_pt i 0 = (vx i, vy i)" unfolding edge_pt_def by (by100 simp)
            have "\<exists>k<?n. (vx i, vy i) = (vx k, vy k)" using hi by (by100 blast)
            have "(SOME k. k < ?n \<and> (vx i, vy i) = (vx k, vy k)) = i"
              by (rule some_equality) (use hi hC3 in \<open>(by100 blast)+\<close>)
            thus ?thesis unfolding q_def hvi using \<open>\<exists>k<?n. _\<close> by (by100 auto)
          qed
          show ?thesis
          proof (cases "snd(scheme!i) = snd(scheme!j)")
            case True \<comment> \<open>Same direction, t=0: need vtgt i = vtgt j.\<close>
            have hdir_eq: "snd(scheme!i) = snd(scheme!(partner i))" using True hpi by (by100 simp)
            have "(i, j) \<in> vtx_id"
            proof -
              have "(i, j) \<in> (let jj = partner i in if snd(scheme!i) = snd(scheme!jj)
                then {(i, jj), (Suc i mod ?n, Suc jj mod ?n)}
                else {(i, Suc jj mod ?n), (Suc i mod ?n, jj)})"
                using hpi hdir_eq by (by100 simp)
              thus ?thesis unfolding vtx_id_def using hi by (by100 blast)
            qed
            hence "(i, j) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 auto)
            hence "vtgt i = vtgt j" by (rule vtgt_class)
            have hq_vj: "q (edge_pt j 0) = (vx (vtgt j), vy (vtgt j))"
            proof -
              have hvj: "edge_pt j 0 = (vx j, vy j)" unfolding edge_pt_def by (by100 simp)
              have "\<exists>k<?n. (vx j, vy j) = (vx k, vy k)" using hj by (by100 blast)
              have "(SOME k. k < ?n \<and> (vx j, vy j) = (vx k, vy k)) = j"
                by (rule some_equality) (use hj hC3 in \<open>(by100 blast)+\<close>)
              thus ?thesis unfolding q_def hvj using \<open>\<exists>k<?n. _\<close> by (by100 auto)
            qed
            from hq_vi hq_vj \<open>vtgt i = vtgt j\<close>
            have "q (edge_pt i 0) = q (edge_pt j 0)" by (by100 simp)
            thus ?thesis using ht0 True unfolding edge_pt_def by (by100 simp)
          next
            case False \<comment> \<open>Opposite direction, t=0: need vtgt i = vtgt(Suc j mod n).\<close>
            have hn_gt: "?n > 0" using assms by (by100 linarith)
            have hjm: "Suc j mod ?n < ?n" using hn_gt by (by100 simp)
            have hdir_ne: "snd(scheme!i) \<noteq> snd(scheme!(partner i))" using False hpi by (by100 simp)
            have "(i, Suc j mod ?n) \<in> vtx_id"
            proof -
              have "(i, Suc j mod ?n) \<in> (let jj = partner i in if snd(scheme!i) = snd(scheme!jj)
                then {(i, jj), (Suc i mod ?n, Suc jj mod ?n)}
                else {(i, Suc jj mod ?n), (Suc i mod ?n, jj)})"
                using hpi hdir_ne by (by100 simp)
              thus ?thesis unfolding vtx_id_def using hi by (by100 blast)
            qed
            hence "(i, Suc j mod ?n) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 auto)
            hence "vtgt i = vtgt (Suc j mod ?n)" by (rule vtgt_class)
            have hq_vjm: "q (edge_pt j 1) = (vx (vtgt (Suc j mod ?n)), vy (vtgt (Suc j mod ?n)))"
            proof -
              have hedge_j1_0: "edge_pt j 1 = (vx (Suc j mod ?n), vy (Suc j mod ?n))"
                unfolding edge_pt_def by (by100 simp)
              have hexk_jm0: "\<exists>k<?n. (vx (Suc j mod ?n), vy (Suc j mod ?n)) = (vx k, vy k)"
                using hjm by (by100 blast)
              have hsome_jm0: "(SOME k. k < ?n \<and> (vx (Suc j mod ?n), vy (Suc j mod ?n)) = (vx k, vy k)) = Suc j mod ?n"
                by (rule some_equality) (use hjm hC3 in \<open>(by100 blast)+\<close>)
              thus ?thesis unfolding q_def hedge_j1_0 Let_def using hexk_jm0 hsome_jm0 by (by100 auto)
            qed
            \<comment> \<open>RHS at t=0 opp\\_dir: q(t*vx j + (1-t)*vx(Suc j), ...) at t=0 = q(vx(Suc j), vy(Suc j)).\<close>
            have "edge_pt j (1 - 0) = edge_pt j 1" by (by100 simp)
            from hq_vi hq_vjm \<open>vtgt i = vtgt (Suc j mod ?n)\<close>
            have "q (edge_pt i 0) = q (edge_pt j 1)" by (by100 simp)
            thus ?thesis using ht0 False unfolding edge_pt_def by (by100 simp)
          qed
        next
          assume ht1: "t = 1"
          \<comment> \<open>LHS: q(v\\_{Suc i mod n}).\<close>
          have hn_gt: "?n > 0" using assms by (by100 linarith)
          have him: "Suc i mod ?n < ?n" using hn_gt by (by100 simp)
          have hq_vim: "q (edge_pt i 1) = (vx (vtgt (Suc i mod ?n)), vy (vtgt (Suc i mod ?n)))"
          proof -
            have hedge_i1: "edge_pt i 1 = (vx (Suc i mod ?n), vy (Suc i mod ?n))"
              unfolding edge_pt_def by (by100 simp)
            have hexk_im: "\<exists>k<?n. (vx (Suc i mod ?n), vy (Suc i mod ?n)) = (vx k, vy k)"
              using him by (by100 blast)
            have hsome_im: "(SOME k. k < ?n \<and> (vx (Suc i mod ?n), vy (Suc i mod ?n)) = (vx k, vy k)) = Suc i mod ?n"
              by (rule some_equality) (use him hC3 in \<open>(by100 blast)+\<close>)
            thus ?thesis unfolding q_def hedge_i1 Let_def using hexk_im hsome_im by (by100 auto)
          qed
          show ?thesis
          proof (cases "snd(scheme!i) = snd(scheme!j)")
            case True \<comment> \<open>Same direction, t=1: need vtgt(Suc i) = vtgt(Suc j).\<close>
            have hjm: "Suc j mod ?n < ?n" using hn_gt by (by100 simp)
            have hdir_eq: "snd(scheme!i) = snd(scheme!(partner i))" using True hpi by (by100 simp)
            have "(Suc i mod ?n, Suc j mod ?n) \<in> vtx_id"
            proof -
              have "(Suc i mod ?n, Suc j mod ?n) \<in> (let jj = partner i in if snd(scheme!i) = snd(scheme!jj)
                then {(i, jj), (Suc i mod ?n, Suc jj mod ?n)}
                else {(i, Suc jj mod ?n), (Suc i mod ?n, jj)})"
                using hpi hdir_eq by (by100 simp)
              thus ?thesis unfolding vtx_id_def using hi by (by100 blast)
            qed
            hence "(Suc i mod ?n, Suc j mod ?n) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 auto)
            hence "vtgt (Suc i mod ?n) = vtgt (Suc j mod ?n)" by (rule vtgt_class)
            have hq_vjm_1: "q (edge_pt j 1) = (vx (vtgt (Suc j mod ?n)), vy (vtgt (Suc j mod ?n)))"
            proof -
              have hedge_j1_1: "edge_pt j 1 = (vx (Suc j mod ?n), vy (Suc j mod ?n))"
                unfolding edge_pt_def by (by100 simp)
              have hexk_jm1: "\<exists>k<?n. (vx (Suc j mod ?n), vy (Suc j mod ?n)) = (vx k, vy k)"
                using hjm by (by100 blast)
              have hsome_jm1: "(SOME k. k < ?n \<and> (vx (Suc j mod ?n), vy (Suc j mod ?n)) = (vx k, vy k)) = Suc j mod ?n"
                by (rule some_equality) (use hjm hC3 in \<open>(by100 blast)+\<close>)
              thus ?thesis unfolding q_def hedge_j1_1 Let_def using hexk_jm1 hsome_jm1 by (by100 auto)
            qed
            from hq_vim hq_vjm_1 \<open>vtgt (Suc i mod ?n) = vtgt (Suc j mod ?n)\<close>
            have "q (edge_pt i 1) = q (edge_pt j 1)" by (by100 simp)
            thus ?thesis using ht1 True unfolding edge_pt_def by (by100 simp)
          next
            case False \<comment> \<open>Opposite direction, t=1: need vtgt(Suc i) = vtgt j.\<close>
            have hdir_ne: "snd(scheme!i) \<noteq> snd(scheme!(partner i))" using False hpi by (by100 simp)
            have "(Suc i mod ?n, j) \<in> vtx_id"
            proof -
              have "(Suc i mod ?n, j) \<in> (let jj = partner i in if snd(scheme!i) = snd(scheme!jj)
                then {(i, jj), (Suc i mod ?n, Suc jj mod ?n)}
                else {(i, Suc jj mod ?n), (Suc i mod ?n, jj)})"
                using hpi hdir_ne by (by100 simp)
              thus ?thesis unfolding vtx_id_def using hi by (by100 blast)
            qed
            hence "(Suc i mod ?n, j) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 auto)
            hence "vtgt (Suc i mod ?n) = vtgt j" by (rule vtgt_class)
            have hq_vj: "q (edge_pt j 0) = (vx (vtgt j), vy (vtgt j))"
            proof -
              have hvj: "edge_pt j 0 = (vx j, vy j)" unfolding edge_pt_def by (by100 simp)
              have "\<exists>k<?n. (vx j, vy j) = (vx k, vy k)" using hj by (by100 blast)
              have "(SOME k. k < ?n \<and> (vx j, vy j) = (vx k, vy k)) = j"
                by (rule some_equality) (use hj hC3 in \<open>(by100 blast)+\<close>)
              thus ?thesis unfolding q_def hvj using \<open>\<exists>k<?n. _\<close> by (by100 auto)
            qed
            from hq_vim hq_vj \<open>vtgt (Suc i mod ?n) = vtgt j\<close>
            have "q (edge_pt i 1) = q (edge_pt j 0)" by (by100 simp)
            thus ?thesis using ht1 False unfolding edge_pt_def by (by100 simp)
          qed
        qed
      qed
    qed
  qed
  \<comment> \<open>C9: Interior injectivity + boundary identification pattern.\<close>
  have hC9_interior: "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n)))
           \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
  proof (intro ballI impI allI)
    fix p p' assume hp: "p \<in> P" and hp': "p' \<in> P"
      and hinterior: "\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))"
      and hqeq: "q p = q p'"
    \<comment> \<open>q(p) = p: p is not on any edge, so the \\<exists> in q\\_def is false.\<close>
    have hqp: "q p = p"
    proof -
      \<comment> \<open>p is not a vertex (vertex v\\_k = edge\\_pt k 0 is on edge k at t=0).\<close>
      have hnotvertex: "\<not>(\<exists>k<?n. p = (vx k, vy k))"
      proof
        assume "\<exists>k<?n. p = (vx k, vy k)"
        then obtain k where "k < ?n" "p = (vx k, vy k)" by (by100 blast)
        hence "p = ((1-0)*vx k + 0*vx(Suc k mod ?n), (1-0)*vy k + 0*vy(Suc k mod ?n))" by (by100 simp)
        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        ultimately show False using hinterior \<open>k < ?n\<close> by (by100 blast)
      qed
      \<comment> \<open>p is not on any non-canonical edge interior.\<close>
      have hnotedge: "\<not>(\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p = edge_pt i t \<and> \<not> is_canonical i)"
      proof
        assume "\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p = edge_pt i t \<and> \<not> is_canonical i"
        then obtain i t where "i < ?n" "0 < t" "t < 1" "p = edge_pt i t" by (by100 blast)
        have "t \<in> I_set" using \<open>0 < t\<close> \<open>t < 1\<close>
          unfolding top1_unit_interval_def by (by100 simp)
        have "p = ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))"
          using \<open>p = edge_pt i t\<close> unfolding edge_pt_def by (by100 simp)
        thus False using hinterior \<open>i < ?n\<close> \<open>t \<in> I_set\<close> by (by100 blast)
      qed
      show ?thesis unfolding q_def using hnotvertex hnotedge by (by100 auto)
    qed
    \<comment> \<open>Now p = q(p) = q(p'). If p' is also not on any non-canonical edge, q(p') = p'.\<close>
    show "p = p'"
    proof (cases "\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i")
      case False
      have "q p' = p'"
      proof (cases "\<exists>k<?n. p' = (vx k, vy k)")
        case True \<comment> \<open>p' is a vertex v\\_k. Edge k must be canonical (else on non-canon edge).\<close>
        then obtain k where hk: "k < ?n" "p' = (vx k, vy k)" by (by100 blast)
        have "is_canonical k"
        proof (rule ccontr)
          assume "\<not> is_canonical k"
          have "p' = edge_pt k 0" unfolding edge_pt_def using hk(2) by (by100 simp)
          hence "\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i"
            using hk(1) \<open>\<not> is_canonical k\<close> by (by100 force)
          with False show False by (by100 blast)
        qed
        \<comment> \<open>q(p') enters vertex branch. q(p') = v\\_{vtgt k} which is an edge point.
           Since p is interior (not on any edge), p \\<noteq> q(p'). But p = q(p) = q(p'). Contradiction.\<close>
        have hvtgt_k: "vtgt k \<le> k"
          unfolding vtgt_def by (rule Least_le) (by100 simp)
        hence "vtgt k < ?n" using hk(1) by (by100 linarith)
        have "(SOME k'. k' < ?n \<and> p' = (vx k', vy k')) = k"
          by (rule some_equality) (use hk hC3 in \<open>(by100 blast)+\<close>)
        hence hq_vtgt: "q p' = (vx (vtgt k), vy (vtgt k))"
          unfolding q_def using True by (by100 auto)
        have "p = q p'" using hqeq hqp by (by100 simp)
        hence "p = ((1-0)*vx(vtgt k) + 0*vx(Suc(vtgt k) mod ?n),
                     (1-0)*vy(vtgt k) + 0*vy(Suc(vtgt k) mod ?n))"
          using hq_vtgt by (by100 simp)
        moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        ultimately have False using hinterior \<open>vtgt k < ?n\<close> by (by100 blast)
        thus ?thesis by (by100 simp)
      next
        case vF: False
        have "\<not>(\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i)"
          using \<open>\<not>(\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i)\<close>
          by (by100 force)
        thus ?thesis unfolding q_def using vF by (by100 auto)
      qed
      thus ?thesis using hqeq hqp by (by100 simp)
    next
      case True
      \<comment> \<open>p' is on a non-canonical edge. q(p') is on a canonical edge.
         But p = q(p') is interior (not on any edge). Contradiction.\<close>
      \<comment> \<open>Need: partner(i) < n, q(p') = edge\\_pt(partner i, ...).
         Then q(p') is on edge partner(i), contradicting p = q(p') being interior.\<close>
      \<comment> \<open>p' on non-canonical edge: q(p') enters the THEN branch of q\\_def.
         q(p') = edge\\_pt(partner(SOME...), t') for some t'.
         This is a point on a canonical edge. But p is interior (not on any edge).
         So p \\<noteq> q(p'), contradicting p = q(p) = q(p').\<close>
      \<comment> \<open>Key: any value returned by the THEN branch of q is an edge point.\<close>
      have q_then_on_edge: "\<And>p0. (\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i) \<Longrightarrow>
        \<exists>j t'. j < ?n \<and> 0 \<le> t' \<and> t' \<le> 1 \<and> q p0 = edge_pt j t'"
      proof -
        fix p0 assume hex: "\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i"
        then obtain i0 t0 where hi0: "i0 < ?n" "0 \<le> t0" "t0 \<le> 1" "p0 = edge_pt i0 t0" "\<not> is_canonical i0"
          by (by100 blast)
        \<comment> \<open>Case: is p0 a vertex?\<close>
        show "\<exists>j t'. j < ?n \<and> 0 \<le> t' \<and> t' \<le> 1 \<and> q p0 = edge_pt j t'"
        proof (cases "\<exists>k<?n. p0 = (vx k, vy k)")
          case True \<comment> \<open>p0 is a vertex v\\_k. q enters vertex branch.\<close>
          then obtain k where hk: "k < ?n" "p0 = (vx k, vy k)" by (by100 blast)
          have "(SOME k'. k' < ?n \<and> p0 = (vx k', vy k')) = k"
            by (rule some_equality) (use hk hC3 in \<open>(by100 blast)+\<close>)
          hence hq_eq: "q p0 = (vx (vtgt k), vy (vtgt k))"
            unfolding q_def using True by (by100 auto)
          \<comment> \<open>vtgt k < n (need partner properties).\<close>
          have "vtgt k < ?n"
          proof -
            have "(k, k) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 simp)
            hence "vtgt k \<le> k" unfolding vtgt_def by (rule Least_le)
            thus ?thesis using hk(1) by (by100 linarith)
          qed
          hence "q p0 = edge_pt (vtgt k) 0" using hq_eq unfolding edge_pt_def by (by100 simp)
          thus ?thesis using \<open>vtgt k < ?n\<close> by (by100 force)
        next
          case vF: False \<comment> \<open>p0 is not a vertex. Must be edge interior (0 < t < 1).\<close>
          have "0 < t0 \<and> t0 < 1"
          proof -
            have "t0 \<noteq> 0"
            proof
              assume "t0 = 0"
              hence "p0 = (vx i0, vy i0)" using hi0(4) unfolding edge_pt_def by (by100 simp)
              hence "\<exists>k<?n. p0 = (vx k, vy k)" using hi0(1) by (by100 blast)
              with vF show False by (by100 blast)
            qed
            moreover have "t0 \<noteq> 1"
            proof
              assume "t0 = 1"
              hence "p0 = (vx (Suc i0 mod ?n), vy (Suc i0 mod ?n))"
                using hi0(4) unfolding edge_pt_def by (by100 simp)
              have "?n > 0" using assms by (by100 linarith)
              hence "Suc i0 mod ?n < ?n" by (by100 simp)
              hence "\<exists>k<?n. p0 = (vx k, vy k)"
                using \<open>p0 = (vx (Suc i0 mod ?n), vy (Suc i0 mod ?n))\<close> by (by100 blast)
              with vF show False by (by100 blast)
            qed
            ultimately show ?thesis using hi0(2) hi0(3) by (by100 linarith)
          qed
          hence hex_interior: "\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i"
            using hi0(1) hi0(4) hi0(5) by (by100 blast)
          \<comment> \<open>q enters the edge interior branch. Same proof as before.\<close>
          define sel where "sel = (SOME (i,t). i < ?n \<and> 0 < t \<and> t < 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i)"
          define i' where "i' = fst sel" define t' where "t' = snd sel"
          have hsel: "i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> p0 = edge_pt i' t' \<and> \<not> is_canonical i'"
          proof -
            from hex_interior have "\<exists>p. (\<lambda>(i,t). i < ?n \<and> 0 < t \<and> t < 1 \<and> p0 = edge_pt i t \<and> \<not> is_canonical i) p"
              by (by100 auto)
            from someI_ex[OF this] show ?thesis unfolding sel_def i'_def t'_def by (by100 auto)
          qed
          have hpartner: "partner i' < ?n"
          proof -
            have hcard: "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} = 2"
            proof -
              have "i' \<in> {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')}" using hsel by (by100 simp)
              have "finite {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')}" by (by100 simp)
              have "{j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} \<noteq> {}" using \<open>i' \<in> _\<close> by (by100 blast)
              have "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} \<noteq> 0"
                using \<open>finite _\<close> \<open>_ \<noteq> {}\<close> by (by100 simp)
              moreover have "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} \<in> {0, 2}"
                using hproper by (by100 blast)
              ultimately show ?thesis
                by (cases "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i')} = 0") (by100 blast)+
            qed
            have "i' < ?n" using hsel by (by100 blast)
            from partner_props[OF this hcard] show ?thesis by (by100 blast)
          qed
          define j where "j = partner i'" define s where "s = (if snd(scheme!i') = snd(scheme!j) then t' else 1 - t')"
          have q_eq: "q p0 = (let (i,t) = sel in let j' = partner i
                 in if snd(scheme!i) = snd(scheme!j') then edge_pt j' t else edge_pt j' (1-t))"
            unfolding q_def sel_def using hex_interior vF by (by100 auto)
          have "sel = (i', t')" unfolding i'_def t'_def by (by100 simp)
          hence "q p0 = edge_pt j s" using q_eq unfolding j_def s_def by (by100 simp)
          moreover have "j < ?n" using hpartner unfolding j_def by (by100 simp)
          moreover have "0 \<le> s" "s \<le> 1" using hsel unfolding s_def by (by100 auto)+
          ultimately show ?thesis by (by100 blast)
        qed
      qed
      from True obtain i t where hit: "i < ?n" "0 \<le> t" "t \<le> 1" "p' = edge_pt i t" "\<not> is_canonical i"
        by (by100 blast)
      have hex: "\<exists>i t. i < ?n \<and> 0 \<le> t \<and> t \<le> 1 \<and> p' = edge_pt i t \<and> \<not> is_canonical i"
        using hit by (by100 blast)
      from q_then_on_edge[OF hex]
      obtain j t' where hjt: "j < ?n" "0 \<le> t'" "t' \<le> 1" "q p' = edge_pt j t'" by (by100 blast)
      have "t' \<in> I_set" using hjt unfolding top1_unit_interval_def by (by100 simp)
      have "q p' = ((1-t')*vx j + t'*vx(Suc j mod ?n), (1-t')*vy j + t'*vy(Suc j mod ?n))"
        using hjt(4) unfolding edge_pt_def by (by100 simp)
      hence "p \<noteq> q p'" using hinterior hjt(1) \<open>t' \<in> I_set\<close> by (by100 blast)
      thus ?thesis using hqeq hqp by (by100 simp)
    qed
  qed
  have hC9_boundary: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s\<in>{0<..<(1::real)}.
          q ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))
        = q ((1-s)*vx j + s*vx(Suc j mod ?n), (1-s)*vy j + s*vy(Suc j mod ?n))
        \<longrightarrow> (i=j \<and> t=s) \<or> (fst(scheme!i) = fst(scheme!j) \<and>
             (if snd(scheme!i) = snd(scheme!j) then s=t else s=1-t))"
  proof (intro allI impI ballI)
    fix i j t s
    assume hi9: "i < ?n" and hj9: "j < ?n"
      and ht9: "t \<in> {0<..<(1::real)}" and hs9: "s \<in> {0<..<(1::real)}"
    assume hqeq9: "q ((1-t)*vx i + t*vx(Suc i mod ?n), (1-t)*vy i + t*vy(Suc i mod ?n))
        = q ((1-s)*vx j + s*vx(Suc j mod ?n), (1-s)*vy j + s*vy(Suc j mod ?n))"
    have ht_i: "0 < t" "t < 1" using ht9 by (by100 auto)+
    have hs_i: "0 < s" "s < 1" using hs9 by (by100 auto)+
    have ht01: "0 \<le> t" "t \<le> 1" using ht_i by (by100 linarith)+
    have hs01: "0 \<le> s" "s \<le> 1" using hs_i by (by100 linarith)+
    have hqep: "q (edge_pt i t) = q (edge_pt j s)" using hqeq9 unfolding edge_pt_def by (by100 simp)
    show "(i=j \<and> t=s) \<or> (fst(scheme!i) = fst(scheme!j) \<and>
           (if snd(scheme!i) = snd(scheme!j) then s=t else s=1-t))"
    \<comment> \<open>Both t, s \\<in> (0,1) so we're always in the interior case.\<close>
    proof -
      \<comment> \<open>Interior case: q maps each edge point to a canonical edge point.
         For canonical i: q(edge\\_pt i t) = edge\\_pt i t.
         For non-canonical i: q(edge\\_pt i t) = edge\\_pt(partner i, matching\\_t).
         Use hedge\\_unique on the q-images to determine the relationship.\<close>
      \<comment> \<open>q(edge\\_pt i t) is not a vertex.\<close>
      have hv_i: "\<not>(\<exists>k<?n. edge_pt i t = (vx k, vy k))"
        using hnotvertex_gen[OF hi9 ht_i(1) ht_i(2)] .
      have hv_j: "\<not>(\<exists>k<?n. edge_pt j s = (vx k, vy k))"
        using hnotvertex_gen[OF hj9 hs_i(1) hs_i(2)] .
      \<comment> \<open>Determine what q does on each edge point.\<close>
      have hqi9: "q (edge_pt i t) = (if \<not> is_canonical i then
        (if snd(scheme!i) = snd(scheme!(partner i))
          then edge_pt (partner i) t else edge_pt (partner i) (1-t))
        else edge_pt i t)"
      proof (cases "is_canonical i")
        case True
        \<comment> \<open>i canonical: q enters else branch (identity).\<close>
        have "\<not>(\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i')"
        proof
          assume "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i'"
          then obtain i' t' where "i' < ?n" "0 < t'" "t' < 1" "edge_pt i t = edge_pt i' t'" "\<not> is_canonical i'"
            by (by100 blast)
          from hedge_unique[OF hi9 \<open>i' < ?n\<close> ht_i(1) ht_i(2) \<open>0 < t'\<close> \<open>t' < 1\<close> \<open>edge_pt i t = edge_pt i' t'\<close>]
          have "i = i'" by (by100 simp)
          thus False using True \<open>\<not> is_canonical i'\<close> by (by100 simp)
        qed
        thus ?thesis unfolding q_def using hv_i True by (by100 auto)
      next
        case False
        \<comment> \<open>i non-canonical: q enters edge-interior branch.\<close>
        have hex_i: "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i'"
          using hi9 ht_i False by (by100 blast)
        \<comment> \<open>The SOME picks (i, t) by uniqueness.\<close>
        define sel_i where "sel_i = (SOME (i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i')"
        have hsel_i: "fst sel_i < ?n \<and> 0 < snd sel_i \<and> snd sel_i < 1 \<and>
            edge_pt i t = edge_pt (fst sel_i) (snd sel_i) \<and> \<not> is_canonical (fst sel_i)"
        proof -
          from hex_i have "\<exists>p. (\<lambda>(i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt i t = edge_pt i' t' \<and> \<not> is_canonical i') p"
            by (by100 auto)
          from someI_ex[OF this] show ?thesis unfolding sel_i_def by (by100 auto)
        qed
        have "fst sel_i = i \<and> snd sel_i = t"
        proof -
          from hsel_i have "fst sel_i < ?n" "0 < snd sel_i" "snd sel_i < 1" "edge_pt i t = edge_pt (fst sel_i) (snd sel_i)"
            by (by100 auto)+
          from hedge_unique[OF hi9 this(1) ht_i(1) ht_i(2) this(2) this(3) this(4)]
          show ?thesis by (by100 simp)
        qed
        have "q (edge_pt i t) = (let (i',t') = sel_i in let j' = partner i' in
            if snd(scheme!i') = snd(scheme!j') then edge_pt j' t' else edge_pt j' (1-t'))"
          unfolding q_def sel_i_def using hex_i hv_i by (by100 auto)
        also have "\<dots> = (if snd(scheme!i) = snd(scheme!(partner i))
            then edge_pt (partner i) t else edge_pt (partner i) (1-t))"
        proof -
          have "sel_i = (fst sel_i, snd sel_i)" by (by100 simp)
          hence "sel_i = (i, t)" using \<open>fst sel_i = i \<and> snd sel_i = t\<close> by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        finally show ?thesis using False by (by100 simp)
      qed
      \<comment> \<open>Similarly for j.\<close>
      have hqj9: "q (edge_pt j s) = (if \<not> is_canonical j then
        (if snd(scheme!j) = snd(scheme!(partner j))
          then edge_pt (partner j) s else edge_pt (partner j) (1-s))
        else edge_pt j s)"
      proof (cases "is_canonical j")
        case True
        have "\<not>(\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i')"
        proof
          assume "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i'"
          then obtain i' t' where "i' < ?n" "0 < t'" "t' < 1" "edge_pt j s = edge_pt i' t'" "\<not> is_canonical i'"
            by (by100 blast)
          from hedge_unique[OF hj9 \<open>i' < ?n\<close> hs_i(1) hs_i(2) \<open>0 < t'\<close> \<open>t' < 1\<close> \<open>edge_pt j s = edge_pt i' t'\<close>]
          have "j = i'" by (by100 simp)
          thus False using True \<open>\<not> is_canonical i'\<close> by (by100 simp)
        qed
        thus ?thesis unfolding q_def using hv_j True by (by100 auto)
      next
        case False
        have hex_j: "\<exists>i' t'. i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i'"
          using hj9 hs_i False by (by100 blast)
        define sel_j where "sel_j = (SOME (i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i')"
        have hsel_j: "fst sel_j < ?n \<and> 0 < snd sel_j \<and> snd sel_j < 1 \<and>
            edge_pt j s = edge_pt (fst sel_j) (snd sel_j) \<and> \<not> is_canonical (fst sel_j)"
        proof -
          from hex_j have "\<exists>p. (\<lambda>(i',t'). i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j s = edge_pt i' t' \<and> \<not> is_canonical i') p"
            by (by100 auto)
          from someI_ex[OF this] show ?thesis unfolding sel_j_def by (by100 auto)
        qed
        have "fst sel_j = j \<and> snd sel_j = s"
        proof -
          from hsel_j have "fst sel_j < ?n" "0 < snd sel_j" "snd sel_j < 1" "edge_pt j s = edge_pt (fst sel_j) (snd sel_j)"
            by (by100 auto)+
          from hedge_unique[OF hj9 this(1) hs_i(1) hs_i(2) this(2) this(3) this(4)]
          show ?thesis by (by100 simp)
        qed
        have "q (edge_pt j s) = (let (i',t') = sel_j in let j' = partner i' in
            if snd(scheme!i') = snd(scheme!j') then edge_pt j' t' else edge_pt j' (1-t'))"
          unfolding q_def sel_j_def using hex_j hv_j by (by100 auto)
        also have "\<dots> = (if snd(scheme!j) = snd(scheme!(partner j))
            then edge_pt (partner j) s else edge_pt (partner j) (1-s))"
        proof -
          have "sel_j = (fst sel_j, snd sel_j)" by (by100 simp)
          hence "sel_j = (j, s)" using \<open>fst sel_j = j \<and> snd sel_j = s\<close> by (by100 simp)
          thus ?thesis by (by100 simp)
        qed
        finally show ?thesis using False by (by100 simp)
      qed
      \<comment> \<open>Now: q(edge\\_pt i t) is edge\\_pt(ci, ct) and q(edge\\_pt j s) is edge\\_pt(cj, cs)
         for canonical edges ci, cj. By hedge\\_unique: ci=cj and ct=cs.\<close>
      define ci where "ci = (if is_canonical i then i else partner i)"
      define ct where "ct = (if is_canonical i then t
          else if snd(scheme!i) = snd(scheme!(partner i)) then t else 1-t)"
      define cj where "cj = (if is_canonical j then j else partner j)"
      define cs where "cs = (if is_canonical j then s
          else if snd(scheme!j) = snd(scheme!(partner j)) then s else 1-s)"
      have "q (edge_pt i t) = edge_pt ci ct" using hqi9 unfolding ci_def ct_def by (by100 auto)
      have "q (edge_pt j s) = edge_pt cj cs" using hqj9 unfolding cj_def cs_def by (by100 auto)
      from hqep \<open>q (edge_pt i t) = edge_pt ci ct\<close> \<open>q (edge_pt j s) = edge_pt cj cs\<close>
      have "edge_pt ci ct = edge_pt cj cs" by (by100 simp)
      have "0 < ct" "ct < 1" unfolding ct_def using ht_i by (by100 auto)+
      have "0 < cs" "cs < 1" unfolding cs_def using hs_i by (by100 auto)+
      have hci_lt: "ci < ?n"
      proof (cases "is_canonical i")
        case True thus ?thesis unfolding ci_def using hi9 by (by100 simp)
      next
        case False
        have hcard_i: "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} = 2"
        proof -
          have "i \<in> {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)}" using hi9 by (by100 simp)
          have "finite {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)}" by (by100 simp)
          hence "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} \<noteq> 0"
            using \<open>i \<in> _\<close> by (by100 auto)
          moreover have "card {j. j < ?n \<and> fst(scheme!j) = fst(scheme!i)} \<in> {0, 2}"
            using hproper by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        from partner_props[OF hi9 hcard_i] show ?thesis unfolding ci_def using False by (by100 simp)
      qed
      have hcj_lt: "cj < ?n"
      proof (cases "is_canonical j")
        case True thus ?thesis unfolding cj_def using hj9 by (by100 simp)
      next
        case False
        have hcard_j: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} = 2"
        proof -
          have "j \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" using hj9 by (by100 simp)
          have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" by (by100 simp)
          hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<noteq> 0"
            using \<open>j \<in> _\<close> by (by100 auto)
          moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<in> {0, 2}"
            using hproper by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        from partner_props[OF hj9 hcard_j] show ?thesis unfolding cj_def using False by (by100 simp)
      qed
      from hedge_unique[OF hci_lt hcj_lt \<open>0 < ct\<close> \<open>ct < 1\<close> \<open>0 < cs\<close> \<open>cs < 1\<close> \<open>edge_pt ci ct = edge_pt cj cs\<close>]
      have "ci = cj" "ct = cs" by (by100 auto)+
      \<comment> \<open>Recover i, j, t, s from ci, cj, ct, cs.\<close>
      show ?thesis
      proof (cases "is_canonical i")
        case hiC: True
        hence "ci = i" "ct = t" unfolding ci_def ct_def by (by100 auto)+
        show ?thesis
        proof (cases "is_canonical j")
          case True
          hence "cj = j" "cs = s" unfolding cj_def cs_def by (by100 auto)+
          from \<open>ci = i\<close> \<open>ci = cj\<close> \<open>cj = j\<close> have "i = j" by (by100 simp)
          from \<open>ct = t\<close> \<open>ct = cs\<close> \<open>cs = s\<close> have "t = s" by (by100 simp)
          thus ?thesis using \<open>i = j\<close> \<open>t = s\<close> by (by100 blast)
        next
          case hjNC: False
          hence "cj = partner j" unfolding cj_def by (by100 simp)
          from \<open>ci = i\<close> \<open>ci = cj\<close> \<open>cj = partner j\<close> have hip: "i = partner j" by (by100 simp)
          \<comment> \<open>Same label: partner j has same label as j.\<close>
          have hcard_j2: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} = 2"
          proof -
            have "j \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" using hj9 by (by100 simp)
            have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" by (by100 simp)
            hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<noteq> 0"
              using \<open>j \<in> _\<close> by (by100 auto)
            moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<in> {0, 2}"
              using hproper by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          from partner_props[OF hj9 hcard_j2]
          have "fst(scheme!(partner j)) = fst(scheme!j)" by (by100 blast)
          hence "fst(scheme!i) = fst(scheme!j)" using hip by (by100 simp)
          moreover have "if snd(scheme!i) = snd(scheme!j) then s=t else s=1-t"
          proof (cases "snd(scheme!j) = snd(scheme!(partner j))")
            case True
            hence "cs = s" unfolding cs_def using hjNC by (by100 simp)
            from \<open>ct = t\<close> \<open>ct = cs\<close> this have "t = s" by (by100 simp)
            have "snd(scheme!i) = snd(scheme!j)" using True hip by (by100 simp)
            thus ?thesis using \<open>t = s\<close> by (by100 simp)
          next
            case False
            hence "cs = 1-s" unfolding cs_def using hjNC by (by100 simp)
            from \<open>ct = t\<close> \<open>ct = cs\<close> this have "t = 1-s" by (by100 simp)
            hence "s = 1-t" by (by100 linarith)
            have "snd(scheme!i) \<noteq> snd(scheme!j)" using False hip by (by100 simp)
            thus ?thesis using \<open>s = 1-t\<close> by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
      next
        case hiNC: False
        hence "ci = partner i" unfolding ci_def by (by100 simp)
        show ?thesis
        proof (cases "is_canonical j")
          case hjC: True
          hence "cj = j" "cs = s" unfolding cj_def cs_def by (by100 auto)+
          from \<open>ci = cj\<close> \<open>ci = partner i\<close> \<open>cj = j\<close> have hjp: "partner i = j" by (by100 simp)
          have hcard_i2: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = 2"
          proof -
            have "i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hi9 by (by100 simp)
            have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" by (by100 simp)
            hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<noteq> 0"
              using \<open>i \<in> _\<close> by (by100 auto)
            moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<in> {0, 2}"
              using hproper by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          from partner_props[OF hi9 hcard_i2]
          have "fst(scheme!(partner i)) = fst(scheme!i)" by (by100 blast)
          hence "fst(scheme!i) = fst(scheme!j)" using hjp by (by100 simp)
          moreover have "if snd(scheme!i) = snd(scheme!j) then s=t else s=1-t"
          proof (cases "snd(scheme!i) = snd(scheme!(partner i))")
            case True
            hence "ct = t" unfolding ct_def using hiNC by (by100 simp)
            from this \<open>ct = cs\<close> \<open>cs = s\<close> have "t = s" by (by100 simp)
            have "snd(scheme!i) = snd(scheme!j)" using True hjp by (by100 simp)
            thus ?thesis using \<open>t = s\<close> by (by100 simp)
          next
            case False
            hence "ct = 1-t" unfolding ct_def using hiNC by (by100 simp)
            from this \<open>ct = cs\<close> \<open>cs = s\<close> have "1-t = s" by (by100 simp)
            have "snd(scheme!i) \<noteq> snd(scheme!j)" using False hjp by (by100 simp)
            thus ?thesis using \<open>1-t = s\<close> by (by100 simp)
          qed
          ultimately show ?thesis by (by100 blast)
        next
          case hjNC: False
          hence "cj = partner j" unfolding cj_def by (by100 simp)
          from \<open>ci = cj\<close> \<open>ci = partner i\<close> \<open>cj = partner j\<close> have hpp: "partner i = partner j" by (by100 simp)
          \<comment> \<open>partner i = partner j implies i = j (label uniqueness: card = 2).\<close>
          have "i = j"
          proof -
            have hcard_i3: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} = 2"
            proof -
              have "i \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" using hi9 by (by100 simp)
              have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)}" by (by100 simp)
              hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<noteq> 0"
                using \<open>i \<in> _\<close> by (by100 auto)
              moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!i)} \<in> {0, 2}"
                using hproper by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            from partner_props[OF hi9 hcard_i3]
            have hpi: "partner i < ?n" "partner i \<noteq> i" "fst(scheme!(partner i)) = fst(scheme!i)" by (by100 blast)+
            have hcard_j3: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} = 2"
            proof -
              have "j \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" using hj9 by (by100 simp)
              have "finite {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)}" by (by100 simp)
              hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<noteq> 0"
                using \<open>j \<in> _\<close> by (by100 auto)
              moreover have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!j)} \<in> {0, 2}"
                using hproper by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            from partner_props[OF hj9 hcard_j3]
            have hpj: "partner j < ?n" "partner j \<noteq> j" "fst(scheme!(partner j)) = fst(scheme!j)" by (by100 blast)+
            \<comment> \<open>i, j, partner i = partner j = k all have the same label.\<close>
            define k where "k = partner i"
            have "fst(scheme!i) = fst(scheme!k)" using hpi(3) unfolding k_def by (by100 simp)
            have "fst(scheme!j) = fst(scheme!k)" using hpj(3) hpp unfolding k_def by (by100 simp)
            hence "fst(scheme!i) = fst(scheme!j)" using \<open>fst(scheme!i) = fst(scheme!k)\<close> by (by100 simp)
            \<comment> \<open>{k, i, j} \\<subseteq> the 2-element label set. Since k \\<noteq> i and k \\<noteq> j: i = j.\<close>
            have "k \<in> {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}"
              using hpi(1) \<open>fst(scheme!i) = fst(scheme!k)\<close> unfolding k_def by (by100 simp)
            have "i \<in> {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}" using hi9 by (by100 simp)
            have "j \<in> {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}"
              using hj9 \<open>fst(scheme!i) = fst(scheme!j)\<close> by (by100 simp)
            have "{k, i, j} \<subseteq> {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}"
              using \<open>k \<in> _\<close> \<open>i \<in> _\<close> \<open>j \<in> _\<close> by (by100 blast)
            have "k \<noteq> i" using hpi(2) unfolding k_def by (by100 simp)
            have "k \<noteq> j" using hpj(2) hpp unfolding k_def by (by100 simp)
            have "card {k, i, j} \<le> 2" using hcard_i3 \<open>{k, i, j} \<subseteq> _\<close>
            proof -
              have "finite {m. m < ?n \<and> fst(scheme!m) = fst(scheme!i)}" by (by100 simp)
              from card_mono[OF this \<open>{k, i, j} \<subseteq> _\<close>]
              show ?thesis using hcard_i3 by (by100 linarith)
            qed
            \<comment> \<open>card {k, i, j} = 3 if all distinct, but \\<le> 2. So not all distinct: i = j.\<close>
            have "card {k, i} = 2" using \<open>k \<noteq> i\<close> by (by100 simp)
            show "i = j"
            proof (rule ccontr)
              assume "i \<noteq> j"
              hence "card {k, i, j} = 3" using \<open>k \<noteq> i\<close> \<open>k \<noteq> j\<close> by (by100 simp)
              thus False using \<open>card {k, i, j} \<le> 2\<close> by (by100 linarith)
            qed
          qed
          \<comment> \<open>i = j implies ct = cs gives t = s.\<close>
          have "t = s"
          proof -
            from \<open>ct = cs\<close> \<open>i = j\<close>
            show ?thesis unfolding ct_def cs_def
              by (cases "is_canonical i"; cases "snd(scheme!i) = snd(scheme!(partner i))") (by100 auto)+
          qed
          thus ?thesis using \<open>i = j\<close> \<open>t = s\<close> by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>Assembly: introduce witnesses P, q, vx, vy and combine all conditions.\<close>
  \<comment> \<open>Assemble: pack all conditions into the existential.\<close>
  have htopo: "is_topology_on_strict Y TY"
  proof -
    let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
    \<comment> \<open>TY is the quotient topology: U \\<in> TY iff q\\<inverse>(U) \\<cap> P is open in P.\<close>
    \<comment> \<open>Standard: quotient topology is a topology on the quotient set.\<close>
    have htopo_P: "is_topology_on P ?TP"
    proof -
      have "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV]
        by (by100 simp)
      thus ?thesis
        by (rule subspace_topology_is_topology_on) (by100 simp)
    qed
    have hY_eq: "Y = q ` P" unfolding Y_def by (by100 simp)
    \<comment> \<open>is\\_topology\\_on Y TY: Y = \\<Union>TY, TY closed under \\<union> and finite \\<inter>.\<close>
    have "is_topology_on Y TY"
      unfolding is_topology_on_def
    proof (intro conjI allI impI)
      \<comment> \<open>1. \\<emptyset> \\<in> TY.\<close>
      show "{} \<in> TY" unfolding TY_def
      proof (intro CollectI exI[of _ "{}"] conjI)
        show "({} :: (real \<times> real) set) \<subseteq> P" by (by100 simp)
        show "\<forall>x\<in>{}. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> {}" by (by100 simp)
        show "{} = q ` {}" by (by100 simp)
        show "{} \<in> ?TP" using htopo_P unfolding is_topology_on_def by (by100 blast)
      qed
    next
      \<comment> \<open>2. Y \\<in> TY.\<close>
      show "Y \<in> TY" unfolding TY_def
      proof (intro CollectI exI[of _ P] conjI)
        show "P \<subseteq> P" by (by100 simp)
        show "\<forall>x\<in>P. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> P" by (by100 simp)
        show "Y = q ` P" unfolding Y_def by (by100 simp)
        show "P \<in> ?TP" using htopo_P unfolding is_topology_on_def by (by100 blast)
      qed
    next
      \<comment> \<open>3. Arbitrary union.\<close>
      fix U :: "(real \<times> real) set set" assume hU: "U \<subseteq> TY"
      show "\<Union>U \<in> TY"
      proof -
        \<comment> \<open>For each u \\<in> U, get the witness V\\_u.\<close>
        have "\<forall>u\<in>U. \<exists>V. V \<subseteq> P \<and> (\<forall>x\<in>V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V) \<and> u = q ` V \<and> V \<in> ?TP"
          using hU unfolding TY_def by (by100 blast)
        from bchoice[OF this]
        obtain f where hf: "\<forall>u\<in>U. f u \<subseteq> P \<and> (\<forall>x\<in>f u. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> f u) \<and> u = q ` f u \<and> f u \<in> ?TP"
          by (by100 auto)
        define V where "V = \<Union>(f ` U)"
        have hV_sub: "V \<subseteq> P" unfolding V_def using hf by (by100 auto)
        have hV_sat: "\<forall>x\<in>V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V"
          unfolding V_def using hf by (by100 blast)
        have hV_image: "\<Union>U = q ` V"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> \<Union>U"
          then obtain u where hu: "u \<in> U" "x \<in> u" by (by100 blast)
          hence "x \<in> q ` f u" using hf by (by100 blast)
          thus "x \<in> q ` V" unfolding V_def using hu(1) by (by100 blast)
        next
          fix x assume "x \<in> q ` V"
          then obtain p where hp: "p \<in> V" "x = q p" by (by100 blast)
          from hp(1) obtain u where hu: "u \<in> U" "p \<in> f u" unfolding V_def by (by100 blast)
          have "x \<in> u" using hp(2) hu(2) hf hu(1) by (by100 blast)
          thus "x \<in> \<Union>U" using hu(1) by (by100 blast)
        qed
        have hV_open: "V \<in> ?TP"
        proof -
          have "f ` U \<subseteq> ?TP" using hf by (by100 blast)
          hence "\<Union>(f ` U) \<in> ?TP" using htopo_P unfolding is_topology_on_def by (by100 blast)
          thus ?thesis unfolding V_def .
        qed
        show ?thesis unfolding TY_def
          using hV_sub hV_sat hV_image hV_open by (by100 blast)
      qed
    next
      \<comment> \<open>4. Finite intersection.\<close>
      fix F :: "(real \<times> real) set set" assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY"
      show "\<Inter>F \<in> TY"
      proof -
        have hFfin: "finite F" and hFne: "F \<noteq> {}" and hFsub: "F \<subseteq> TY" using hF by auto
        have "\<forall>u\<in>F. \<exists>V. V \<subseteq> P \<and> (\<forall>x\<in>V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V) \<and> u = q ` V \<and> V \<in> ?TP"
          using hFsub unfolding TY_def by (by100 blast)
        from bchoice[OF this]
        obtain f where hf: "\<forall>u\<in>F. f u \<subseteq> P \<and> (\<forall>x\<in>f u. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> f u) \<and> u = q ` f u \<and> f u \<in> ?TP"
          by (by100 auto)
        define V where "V = \<Inter>(f ` F)"
        have hV_sub: "V \<subseteq> P"
        proof -
          from hFne obtain u0 where hu0F: "u0 \<in> F" by (by100 blast)
          have "f u0 \<subseteq> P" using hf hu0F by (by100 force)
          moreover have "V \<subseteq> f u0" unfolding V_def using \<open>u0 \<in> F\<close> by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        have hV_sat: "\<forall>x\<in>V. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> V"
        proof (intro ballI allI impI)
          fix x y assume hx: "x \<in> V" and hy: "y \<in> P \<and> q y = q x"
          show "y \<in> V" unfolding V_def
          proof (rule InterI)
            fix W assume "W \<in> f ` F"
            then obtain u where hu: "u \<in> F" "W = f u" by (by100 blast)
            have "x \<in> f u" using hx hu(1) unfolding V_def by (by100 blast)
            hence "y \<in> f u" using hf hu(1) hy by (by100 blast)
            thus "y \<in> W" using hu(2) by (by100 simp)
          qed
        qed
        \<comment> \<open>q`V = \\<Inter>F: uses saturation to distribute image over intersection.\<close>
        have hV_image: "\<Inter>F = q ` V"
        proof (rule set_eqI, rule iffI)
          fix x assume hx: "x \<in> \<Inter>F"
          \<comment> \<open>x \\<in> every u \\<in> F, so x = q(p\\_u) for some p\\_u \\<in> f u.
             Pick any u0 \\<in> F. p\\_{u0} \\<in> f u0. For any other u \\<in> F:
             x \\<in> u = q`(f u), so x = q(p\\_u) for some p\\_u \\<in> f u.
             q(p\\_{u0}) = x = q(p\\_u). By saturation of f u: p\\_{u0} \\<in> f u.
             So p\\_{u0} \\<in> \\<Inter>(f ` F) = V.\<close>
          from hFne obtain u0 where hu0: "u0 \<in> F" by (by100 blast)
          from hx hu0 have "x \<in> u0" by (by100 blast)
          have "u0 = q ` f u0" using hf hu0 by (by100 blast)
          hence "x \<in> q ` f u0" using \<open>x \<in> u0\<close> by (by100 simp)
          from this obtain p0 where hp0: "p0 \<in> f u0" "x = q p0" by (by100 blast)
          have "p0 \<in> V" unfolding V_def
          proof (rule InterI)
            fix W assume "W \<in> f ` F"
            then obtain u where hu: "u \<in> F" "W = f u" by (by100 blast)
            have "x \<in> u" using hx hu(1) by (by100 blast)
            have "u = q ` f u" using hf hu(1) by (by100 blast)
            hence "x \<in> q ` f u" using \<open>x \<in> u\<close> by (by100 simp)
            then obtain pu where hpu: "pu \<in> f u" "x = q pu" by (by100 blast)
            have "q p0 = q pu" using hp0(2) hpu(2) by (by100 simp)
            have "f u0 \<subseteq> P" using hf hu0 by (by100 force)
            hence "p0 \<in> P" using hp0(1) by (by100 blast)
            \<comment> \<open>By saturation of f u: pu \\<in> f u, q(p0)=q(pu), p0 \\<in> P \\<Longrightarrow> p0 \\<in> f u.\<close>
            have sat_u: "\<forall>x\<in>f u. \<forall>y. y \<in> P \<and> q y = q x \<longrightarrow> y \<in> f u"
              using hf hu(1) by (by100 blast)
            have "p0 \<in> f u" using sat_u hpu(1) \<open>p0 \<in> P\<close> \<open>q p0 = q pu\<close> by (by100 blast)
            thus "p0 \<in> W" using hu(2) by (by100 simp)
          qed
          thus "x \<in> q ` V" using hp0(2) by (by100 blast)
        next
          fix x assume "x \<in> q ` V"
          then obtain p where hp: "p \<in> V" "x = q p" by (by100 blast)
          show "x \<in> \<Inter>F"
          proof (rule InterI)
            fix u assume hu: "u \<in> F"
            have "p \<in> f u" using hp(1) hu unfolding V_def by (by100 blast)
            hence "q p \<in> q ` f u" by (by100 blast)
            hence "q p \<in> u" using hf hu by (by100 blast)
            thus "x \<in> u" using hp(2) by (by100 simp)
          qed
        qed
        have hV_open: "V \<in> ?TP"
        proof -
          have "f ` F \<subseteq> ?TP" using hf by (by100 blast)
          moreover have "finite (f ` F)" using hFfin by (by100 simp)
          moreover have "f ` F \<noteq> {}" using hFne by (by100 simp)
          ultimately have "\<Inter>(f ` F) \<in> ?TP"
            using htopo_P unfolding is_topology_on_def by (by100 blast)
          thus ?thesis unfolding V_def .
        qed
        show ?thesis unfolding TY_def
          using hV_sub hV_sat hV_image hV_open by (by100 blast)
      qed
    qed
    moreover have "TY \<subseteq> Pow Y"
    proof
      fix U assume "U \<in> TY"
      then obtain V where "V \<subseteq> P" "U = q ` V" unfolding TY_def by (by100 blast)
      thus "U \<in> Pow Y" unfolding Y_def using \<open>V \<subseteq> P\<close> by (by100 auto)
    qed
    ultimately show ?thesis unfolding is_topology_on_strict_def by (by100 blast)
  qed
  \<comment> \<open>C12: vertex-edge separation. q(vertex) is always a vertex, q(edge interior) is always
     an edge point. By hnotvertex\\_gen, these are disjoint.\<close>
  have hC12: "\<forall>k<?n. \<forall>j<?n. \<forall>ss\<in>{0<..<(1::real)}.
      q (vx k, vy k) \<noteq> q ((1-ss)*vx j + ss*vx(Suc j mod ?n),
                               (1-ss)*vy j + ss*vy(Suc j mod ?n))"
  proof (intro allI impI ballI)
    fix k j :: nat and ss :: real
    assume hk_lt: "k < ?n" and hj_lt: "j < ?n" and hss: "ss \<in> {0<..<(1::real)}"
    have hss1: "0 < ss" and hss2: "ss < 1" using hss by (by100 auto)+
    \<comment> \<open>q(vx k, vy k) = (vx(vtgt k), vy(vtgt k)) — a vertex.\<close>
    have hq_vtx: "q (vx k, vy k) = (vx (vtgt k), vy (vtgt k))"
    proof -
      have "\<exists>k'<?n. (vx k, vy k) = (vx k', vy k')" using hk_lt by (by100 blast)
      hence hbranch: "q (vx k, vy k) = (let k' = (SOME k'. k' < ?n \<and> (vx k, vy k) = (vx k', vy k'))
          in (vx (vtgt k'), vy (vtgt k')))" unfolding q_def by (by100 simp)
      have "(SOME k'. k' < ?n \<and> (vx k, vy k) = (vx k', vy k')) = k"
      proof (rule some_equality)
        show "k < ?n \<and> (vx k, vy k) = (vx k, vy k)" using hk_lt by (by100 simp)
      next
        fix k' assume "k' < ?n \<and> (vx k, vy k) = (vx k', vy k')"
        hence "k' < ?n" "(vx k, vy k) = (vx k', vy k')" by (by100 auto)+
        from hC3[rule_format, OF hk_lt this(1)] this(2) show "k' = k" by (by100 blast)
      qed
      thus ?thesis using hbranch by (by100 simp)
    qed
    \<comment> \<open>q(edge\\_pt(j,ss)) is NOT a vertex (by hnotvertex\\_gen + q definition).\<close>
    have h_ept_not_vtx: "\<not>(\<exists>k'<?n. edge_pt j ss = (vx k', vy k'))"
      using hnotvertex_gen[OF hj_lt hss1 hss2] .
    have hq_not_vtx: "\<not>(\<exists>k'<?n. q (edge_pt j ss) = (vx k', vy k'))"
    proof -
      \<comment> \<open>Branch 1 of q does not apply (edge point \\<noteq> vertex).\<close>
      have hno_b1: "\<not>(\<exists>k'. k' < ?n \<and> edge_pt j ss = (vx k', vy k'))"
        using h_ept_not_vtx by (by100 simp)
      show ?thesis
      proof (cases "\<exists>i t. i < ?n \<and> 0 < t \<and> t < 1 \<and> edge_pt j ss = edge_pt i t \<and> \<not> is_canonical i")
        case False
        \<comment> \<open>Canonical case: q = identity on this point.\<close>
        hence "q (edge_pt j ss) = edge_pt j ss"
          unfolding q_def using hno_b1 by auto
        thus ?thesis using h_ept_not_vtx by (by100 simp)
      next
        case True
        \<comment> \<open>Non-canonical: q maps to partner edge. Extract SOME witness properties.\<close>
        define sel where "sel = (SOME (i,t). i < ?n \<and> 0 < t \<and> t < 1
            \<and> edge_pt j ss = edge_pt i t \<and> \<not> is_canonical i)"
        define i' where "i' = fst sel"
        define t' where "t' = snd sel"
        have hsel: "i' < ?n \<and> 0 < t' \<and> t' < 1 \<and> edge_pt j ss = edge_pt i' t' \<and> \<not> is_canonical i'"
        proof -
          from True have "\<exists>p. (case p of (i,t) \<Rightarrow> i < ?n \<and> 0 < t \<and> t < 1 \<and> edge_pt j ss = edge_pt i t \<and> \<not> is_canonical i)"
            by (by100 auto)
          from someI_ex[OF this] show ?thesis unfolding sel_def i'_def t'_def by (by100 auto)
        qed
        hence hi': "i' < ?n" and ht'1: "0 < t'" and ht'2: "t' < 1" by (by100 auto)+
        define j' where "j' = partner i'"
        have hj': "j' < ?n"
        proof -
          have "card {jj. jj < ?n \<and> fst(scheme!jj) = fst(scheme!i')} \<in> {0, 2}"
            using hproper by (by100 blast)
          moreover have "card {jj. jj < ?n \<and> fst(scheme!jj) = fst(scheme!i')} \<noteq> 0"
          proof -
            have "i' \<in> {jj. jj < ?n \<and> fst(scheme!jj) = fst(scheme!i')}" using hi' by (by100 simp)
            moreover have "finite {jj. jj < ?n \<and> fst(scheme!jj) = fst(scheme!i')}" by (by100 simp)
            ultimately show ?thesis using card_eq_0_iff by auto
          qed
          ultimately have hcard2: "card {jj. jj < ?n \<and> fst(scheme!jj) = fst(scheme!i')} = 2" by (by100 blast)
          from partner_props[OF hi' hcard2] show ?thesis unfolding j'_def by (by100 blast)
        qed
        \<comment> \<open>q result is edge\\_pt(j', t') or edge\\_pt(j', 1-t'). Parameter in (0,1).\<close>
        have hq_eq: "q (edge_pt j ss) = (if snd(scheme!i') = snd(scheme!j') then edge_pt j' t' else edge_pt j' (1-t'))"
        proof -
          \<comment> \<open>q at edge\\_pt: branch 1 excluded, branch 2 applies.\<close>
          have hsel_eq: "sel = (i', t')" unfolding i'_def t'_def by (by100 simp)
          show ?thesis
            unfolding q_def sel_def[symmetric] hsel_eq j'_def using hno_b1 True by auto
        qed
        \<comment> \<open>The result is edge\\_pt at parameter in (0,1), hence not a vertex.\<close>
        show ?thesis
        proof (cases "snd(scheme!i') = snd(scheme!j')")
          case True
          hence "q (edge_pt j ss) = edge_pt j' t'" using hq_eq by (by100 simp)
          from hnotvertex_gen[OF hj' ht'1 ht'2]
          show ?thesis using \<open>q _ = edge_pt j' t'\<close> by (by100 simp)
        next
          case False
          hence "q (edge_pt j ss) = edge_pt j' (1-t')" using hq_eq by (by100 simp)
          have "0 < 1-t'" using ht'2 by (by100 linarith)
          have "1-t' < 1" using ht'1 by (by100 linarith)
          from hnotvertex_gen[OF hj' \<open>0<1-t'\<close> \<open>1-t'<1\<close>]
          show ?thesis using \<open>q _ = edge_pt j' (1-t')\<close> by (by100 simp)
        qed
      qed
    qed
    have hvtgt_lt: "vtgt k < ?n"
    proof -
      \<comment> \<open>k is reachable from k (via Id), so vtgt k \\<le> k < n.\<close>
      have "(k, k) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" by (by100 simp)
      hence hk_reach: "(k, k) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*" .
      have "vtgt k \<le> k" unfolding vtgt_def by (rule Least_le) (by100 simp)
      thus ?thesis using hk_lt by (by100 linarith)
    qed
    have "q (vx k, vy k) \<noteq> q (edge_pt j ss)"
    proof
      assume "q (vx k, vy k) = q (edge_pt j ss)"
      hence "q (edge_pt j ss) = (vx (vtgt k), vy (vtgt k))" using hq_vtx by (by100 simp)
      hence "\<exists>k'<?n. q (edge_pt j ss) = (vx k', vy k')" using hvtgt_lt by (by100 blast)
      thus False using hq_not_vtx by (by100 blast)
    qed
    thus "q (vx k, vy k) \<noteq> q ((1-ss)*vx j + ss*vx(Suc j mod ?n),
                                 (1-ss)*vy j + ss*vy(Suc j mod ?n))"
      unfolding edge_pt_def by (by100 simp)
  qed
  \<comment> \<open>Vertex target: q maps each vertex to some vertex (from hq\\_vtx + hvtgt\\_lt).\<close>
  have hq_vtx_direct: "\<forall>k<?n. q (vx k, vy k) = (vx (vtgt k), vy (vtgt k))"
  proof (intro allI impI)
    fix k assume "k < ?n"
    have "\<exists>k'<?n. (vx k, vy k) = (vx k', vy k')" using \<open>k < ?n\<close> by (by100 blast)
    hence "q (vx k, vy k) = (let k' = (SOME k'. k' < ?n \<and> (vx k, vy k) = (vx k', vy k'))
        in (vx (vtgt k'), vy (vtgt k')))" unfolding q_def by (by100 simp)
    moreover have "(SOME k'. k' < ?n \<and> (vx k, vy k) = (vx k', vy k')) = k"
    proof (rule some_equality)
      show "k < ?n \<and> (vx k, vy k) = (vx k, vy k)" using \<open>k < ?n\<close> by (by100 simp)
    next
      fix k' assume "k' < ?n \<and> (vx k, vy k) = (vx k', vy k')"
      from hC3[rule_format, OF \<open>k<?n\<close>] this show "k' = k" by (by100 blast)
    qed
    ultimately show "q (vx k, vy k) = (vx (vtgt k), vy (vtgt k))" by (by100 simp)
  qed
  have hvtgt_bound: "\<forall>k<?n. vtgt k < ?n"
  proof (intro allI impI)
    fix k assume "k < ?n"
    have "vtgt k \<le> k" unfolding vtgt_def by (rule Least_le) (by100 simp)
    thus "vtgt k < ?n" using \<open>k < ?n\<close> by (by100 linarith)
  qed
  \<comment> \<open>Capture quotient\\_of\\_scheme\\_on for specific Y, TY BEFORE show.\<close>
  have hqos: "top1_quotient_of_scheme_on Y TY scheme"
    unfolding top1_quotient_of_scheme_on_def
    apply (intro conjI)
    apply (rule htopo)
    apply (rule exI[of _ P], rule exI[of _ q], rule exI[of _ vx], rule exI[of _ vy])
    apply (intro conjI)
    using hC1 apply (by100 blast)
    using hC2 apply (by100 blast)
    using hC3 apply (by100 blast)
    using hC4 apply (by100 blast)
    using hC5 apply (by100 simp)
    using hC6 unfolding open01_def apply (by100 blast)
    using hC8 apply (by100 blast)
    using hC9_interior apply (by100 blast)
    using hC9_boundary apply (by100 blast)
    using hC10 apply (by100 blast)
    using hC11 by (by100 blast)
  show ?C1 using hqos by (by100 blast)
  show ?C2
    apply (rule exI[of _ P], rule exI[of _ q], rule exI[of _ vx], rule exI[of _ vy],
           rule exI[of _ Y], rule exI[of _ TY])
    apply (intro conjI)
    using hqos apply (by100 blast)
    using hC1 apply (by100 blast)
    using hC2 apply (by100 blast)
    using hC3 apply (by100 blast)
    using hC4 apply (by100 blast)
    using hC5 apply (by100 simp)
    using hC8 apply (by100 blast)
    using hC9_interior apply (by100 blast)
    using hC9_boundary apply (by100 blast)
    using hC10 apply (by100 blast)
    using hC11 apply (by100 blast)
    using hC12 apply (by100 blast)
    apply (rule exI[of _ vtgt])
  proof (intro conjI allI impI)
    fix k assume hk: "k < ?n"
    show "q (vx k, vy k) = (vx (vtgt k), vy (vtgt k))"
      using hq_vtx_direct[rule_format, OF hk] .
  next
    fix k assume hk: "k < ?n"
    show "vtgt k < ?n" using hvtgt_bound[rule_format, OF hk] .
  next
    fix k assume hk: "k < ?n"
    show "vtgt k \<le> k" unfolding vtgt_def by (rule Least_le) (by100 simp)
  next
    fix k assume hk: "k < ?n"
    \<comment> \<open>Idempotency: vtgt(vtgt(k)) = vtgt(k). Since vtgt(k) is the Least reachable,
       and vtgt(k) is reachable from itself (via Id), vtgt(vtgt(k)) \\<le> vtgt(k).
       But also vtgt(k) is reachable from k, so vtgt(k) is reachable from vtgt(k)
       (reflexivity of rtrancl). So vtgt(vtgt(k)) is the Least of the SAME class as vtgt(k).
       Since vtgt is the Least of k's class, and vtgt(k) is in the same class:
       vtgt(vtgt(k)) = vtgt(k).\<close>
    show "vtgt (vtgt k) = vtgt k"
    proof -
      have hreach: "(k, vtgt k) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
      proof -
        have "\<exists>m. (k, m) \<in> (vtx_id \<union> converse vtx_id \<union> Id)\<^sup>*"
          by (rule exI[of _ k]) (by100 simp)
        thus ?thesis unfolding vtgt_def by (rule LeastI_ex)
      qed
      from vtgt_class[OF hreach] show ?thesis by (by100 simp)
    qed
  next
    \<comment> \<open>vtgt equality implies rtrancl connectivity via C7 vertex identification steps.\<close>
    fix k l assume hk: "k < ?n" and hl: "l < ?n" and hv: "vtgt k = vtgt l"
    \<comment> \<open>vtgt k = vtgt l means both are in the same equivalence class of vtx\\_id.
       The internal vtx\\_id relation is a subset of the output step relation.\<close>
    let ?R = "vtx_id \<union> converse vtx_id \<union> Id"
    let ?S = "{(a, b). \<exists>i<?n. \<exists>j<?n. i \<noteq> j
        \<and> fst (scheme ! i) = fst (scheme ! j)
        \<and> ((snd (scheme ! i) = snd (scheme ! j) \<and> a = i \<and> b = j)
         \<or> (snd (scheme ! i) = snd (scheme ! j) \<and> a = Suc i mod ?n \<and> b = Suc j mod ?n)
         \<or> (snd (scheme ! i) \<noteq> snd (scheme ! j) \<and> a = i \<and> b = Suc j mod ?n)
         \<or> (snd (scheme ! i) \<noteq> snd (scheme ! j) \<and> a = Suc i mod ?n \<and> b = j))}"
    \<comment> \<open>Step 1: (k, vtgt k) \\<in> R* and (l, vtgt l) \\<in> R*.\<close>
    have hk_reach: "(k, vtgt k) \<in> ?R\<^sup>*"
    proof -
      have "\<exists>m. (k, m) \<in> ?R\<^sup>*" by (rule exI[of _ k]) (by100 simp)
      thus ?thesis unfolding vtgt_def by (rule LeastI_ex)
    qed
    have hl_reach: "(l, vtgt l) \<in> ?R\<^sup>*"
    proof -
      have "\<exists>m. (l, m) \<in> ?R\<^sup>*" by (rule exI[of _ l]) (by100 simp)
      thus ?thesis unfolding vtgt_def by (rule LeastI_ex)
    qed
    \<comment> \<open>Step 2: R* is symmetric.\<close>
    have hsymR: "sym (?R\<^sup>*)"
      using sym_rtrancl[of ?R] unfolding sym_def by (by100 blast)
    \<comment> \<open>Step 3: (vtgt k, l) \\<in> R* (from hl\\_reach reversed + hv).\<close>
    have "(vtgt l, l) \<in> ?R\<^sup>*" using hl_reach hsymR unfolding sym_def by (by100 blast)
    hence "(vtgt k, l) \<in> ?R\<^sup>*" using hv by (by100 simp)
    \<comment> \<open>Step 4: (k, l) \\<in> R* (transitivity).\<close>
    have hkl_R: "(k, l) \<in> ?R\<^sup>*"
      using rtrancl_trans[OF hk_reach \<open>(vtgt k, l) \<in> ?R\<^sup>*\<close>] .
    \<comment> \<open>Step 5: vtx\\_id \\<subseteq> ?S (each vtx\\_id pair matches the output step relation).\<close>
    have hvtx_sub: "vtx_id \<subseteq> ?S"
    proof
      fix p assume "p \<in> vtx_id"
      then obtain idx where hidx: "idx < ?n" and
          hp: "p \<in> (let j = partner idx in
            if snd(scheme!idx) = snd(scheme!j) then {(idx, j), (Suc idx mod ?n, Suc j mod ?n)}
            else {(idx, Suc j mod ?n), (Suc idx mod ?n, j)})"
        unfolding vtx_id_def by (by100 auto)
      have hp_lt: "partner idx < ?n" and hp_ne: "partner idx \<noteq> idx"
          and hp_lbl: "fst(scheme!idx) = fst(scheme!(partner idx))"
      proof -
        have "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!idx)} \<in> {0, 2}"
          using hproper by (by100 blast)
        moreover have "idx \<in> {k. k < ?n \<and> fst(scheme!k) = fst(scheme!idx)}" using hidx by (by100 simp)
        hence "{k. k < ?n \<and> fst(scheme!k) = fst(scheme!idx)} \<noteq> {}" by (by100 blast)
        hence "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!idx)} \<noteq> 0" by (by100 simp)
        ultimately have hc2: "card {k. k < ?n \<and> fst(scheme!k) = fst(scheme!idx)} = 2"
          by (by100 blast)
        from partner_props[OF hidx hc2]
        show "partner idx < ?n" and "partner idx \<noteq> idx"
            and "fst(scheme!idx) = fst(scheme!(partner idx))" by (by100 auto)+
      qed
      have hp_ne2: "idx \<noteq> partner idx" using hp_ne by (by100 simp)
      from hp have hp2: "p \<in> (if snd(scheme!idx)=snd(scheme!(partner idx))
          then {(idx, partner idx), (Suc idx mod ?n, Suc (partner idx) mod ?n)}
          else {(idx, Suc (partner idx) mod ?n), (Suc idx mod ?n, partner idx)})"
        unfolding Let_def .
      show "p \<in> ?S"
      proof -
        obtain a b where hab: "p = (a, b)" by (cases p) (by100 simp)
        have "\<exists>i<?n. \<exists>j<?n. i \<noteq> j \<and> fst (scheme ! i) = fst (scheme ! j)
            \<and> ((snd (scheme ! i) = snd (scheme ! j) \<and> a = i \<and> b = j)
             \<or> (snd (scheme ! i) = snd (scheme ! j) \<and> a = Suc i mod ?n \<and> b = Suc j mod ?n)
             \<or> (snd (scheme ! i) \<noteq> snd (scheme ! j) \<and> a = i \<and> b = Suc j mod ?n)
             \<or> (snd (scheme ! i) \<noteq> snd (scheme ! j) \<and> a = Suc i mod ?n \<and> b = j))"
        proof -
          from hp2 hab have "a = idx \<and> b = partner idx \<and> snd(scheme!idx) = snd(scheme!(partner idx))
              \<or> a = Suc idx mod ?n \<and> b = Suc (partner idx) mod ?n \<and> snd(scheme!idx) = snd(scheme!(partner idx))
              \<or> a = idx \<and> b = Suc (partner idx) mod ?n \<and> snd(scheme!idx) \<noteq> snd(scheme!(partner idx))
              \<or> a = Suc idx mod ?n \<and> b = partner idx \<and> snd(scheme!idx) \<noteq> snd(scheme!(partner idx))"
          proof (cases "snd(scheme!idx) = snd(scheme!(partner idx))")
            case True
            from hp2 True have "p \<in> {(idx, partner idx), (Suc idx mod ?n, Suc (partner idx) mod ?n)}"
              by (by100 simp)
            thus ?thesis using True hab by (by100 auto)
          next
            case False
            from hp2 False have "p \<in> {(idx, Suc (partner idx) mod ?n), (Suc idx mod ?n, partner idx)}"
              by (by100 simp)
            thus ?thesis using False hab by (by100 auto)
          qed
          hence "idx \<noteq> partner idx \<and> fst (scheme ! idx) = fst (scheme ! (partner idx))
              \<and> ((snd (scheme ! idx) = snd (scheme ! (partner idx)) \<and> a = idx \<and> b = partner idx)
               \<or> (snd (scheme ! idx) = snd (scheme ! (partner idx)) \<and> a = Suc idx mod ?n \<and> b = Suc (partner idx) mod ?n)
               \<or> (snd (scheme ! idx) \<noteq> snd (scheme ! (partner idx)) \<and> a = idx \<and> b = Suc (partner idx) mod ?n)
               \<or> (snd (scheme ! idx) \<noteq> snd (scheme ! (partner idx)) \<and> a = Suc idx mod ?n \<and> b = partner idx))"
          proof (intro conjI)
            show "idx \<noteq> partner idx" by (rule hp_ne2)
            show "fst (scheme ! idx) = fst (scheme ! (partner idx))" by (rule hp_lbl)
            show "(snd (scheme ! idx) = snd (scheme ! (partner idx)) \<and> a = idx \<and> b = partner idx)
               \<or> (snd (scheme ! idx) = snd (scheme ! (partner idx)) \<and> a = Suc idx mod ?n \<and> b = Suc (partner idx) mod ?n)
               \<or> (snd (scheme ! idx) \<noteq> snd (scheme ! (partner idx)) \<and> a = idx \<and> b = Suc (partner idx) mod ?n)
               \<or> (snd (scheme ! idx) \<noteq> snd (scheme ! (partner idx)) \<and> a = Suc idx mod ?n \<and> b = partner idx)"
            proof (cases "snd (scheme ! idx) = snd (scheme ! (partner idx))")
              case True
              from hp2 True hab
              have "a = idx \<and> b = partner idx \<or> a = Suc idx mod ?n \<and> b = Suc (partner idx) mod ?n"
                by (by100 simp)
              thus ?thesis using True by (by100 blast)
            next
              case False
              from hp2 False hab
              have "a = idx \<and> b = Suc (partner idx) mod ?n \<or> a = Suc idx mod ?n \<and> b = partner idx"
                by (by100 simp)
              thus ?thesis using False by (by100 blast)
            qed
          qed
          hence "\<exists>j<?n. idx \<noteq> j \<and> fst (scheme ! idx) = fst (scheme ! j)
              \<and> ((snd (scheme ! idx) = snd (scheme ! j) \<and> a = idx \<and> b = j)
               \<or> (snd (scheme ! idx) = snd (scheme ! j) \<and> a = Suc idx mod ?n \<and> b = Suc j mod ?n)
               \<or> (snd (scheme ! idx) \<noteq> snd (scheme ! j) \<and> a = idx \<and> b = Suc j mod ?n)
               \<or> (snd (scheme ! idx) \<noteq> snd (scheme ! j) \<and> a = Suc idx mod ?n \<and> b = j))"
            using hp_lt by (by100 blast)
          hence "\<exists>i<?n. \<exists>j<?n. i \<noteq> j \<and> fst (scheme ! i) = fst (scheme ! j)
              \<and> ((snd (scheme ! i) = snd (scheme ! j) \<and> a = i \<and> b = j)
               \<or> (snd (scheme ! i) = snd (scheme ! j) \<and> a = Suc i mod ?n \<and> b = Suc j mod ?n)
               \<or> (snd (scheme ! i) \<noteq> snd (scheme ! j) \<and> a = i \<and> b = Suc j mod ?n)
               \<or> (snd (scheme ! i) \<noteq> snd (scheme ! j) \<and> a = Suc i mod ?n \<and> b = j))"
            using hidx by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
        thus ?thesis using hab by (by100 simp)
      qed
    qed
    \<comment> \<open>Step 6: ?R \\<subseteq> ?S*.\<close>
    have hR_sub_Sstar: "?R\<^sup>* \<subseteq> ?S\<^sup>*"
    proof -
      have "?R \<subseteq> ?S\<^sup>*"
      proof
        fix p assume "p \<in> ?R"
        hence "p \<in> vtx_id \<or> p \<in> converse vtx_id \<or> p \<in> Id" by (by100 blast)
        thus "p \<in> ?S\<^sup>*"
        proof (elim disjE)
          assume "p \<in> vtx_id"
          hence "p \<in> ?S" using hvtx_sub by (by100 blast)
          thus ?thesis by (by100 auto)
        next
          assume "p \<in> converse vtx_id"
          hence "\<exists>a b. p = (a,b) \<and> (b,a) \<in> vtx_id" by auto
          then obtain a b where hp: "p = (a,b)" and hab: "(b,a) \<in> vtx_id" by auto
          have hba: "(b,a) \<in> ?S" using subsetD[OF hvtx_sub hab] .
          hence "p \<in> ?S"
          proof -
            from hba obtain i j where
              hi: "i<?n" and hj: "j<?n" and hne: "i\<noteq>j"
              and hlab: "fst(scheme!i)=fst(scheme!j)"
              and hcases: "(snd(scheme!i)=snd(scheme!j) \<and> b=i \<and> a=j)
                \<or> (snd(scheme!i)=snd(scheme!j) \<and> b=Suc i mod ?n \<and> a=Suc j mod ?n)
                \<or> (snd(scheme!i)\<noteq>snd(scheme!j) \<and> b=i \<and> a=Suc j mod ?n)
                \<or> (snd(scheme!i)\<noteq>snd(scheme!j) \<and> b=Suc i mod ?n \<and> a=j)"
              by (by100 blast)
            \<comment> \<open>Use j, i as witnesses with swapped roles.\<close>
            from hcases
            have "(snd(scheme!j)=snd(scheme!i) \<and> a=j \<and> b=i)
                \<or> (snd(scheme!j)=snd(scheme!i) \<and> a=Suc j mod ?n \<and> b=Suc i mod ?n)
                \<or> (snd(scheme!j)\<noteq>snd(scheme!i) \<and> a=j \<and> b=Suc i mod ?n)
                \<or> (snd(scheme!j)\<noteq>snd(scheme!i) \<and> a=Suc j mod ?n \<and> b=i)"
              by (by100 auto)
            hence "(a,b) \<in> ?S"
            proof -
              assume hswap: "(snd(scheme!j)=snd(scheme!i) \<and> a=j \<and> b=i)
                \<or> (snd(scheme!j)=snd(scheme!i) \<and> a=Suc j mod ?n \<and> b=Suc i mod ?n)
                \<or> (snd(scheme!j)\<noteq>snd(scheme!i) \<and> a=j \<and> b=Suc i mod ?n)
                \<or> (snd(scheme!j)\<noteq>snd(scheme!i) \<and> a=Suc j mod ?n \<and> b=i)"
              have "j<?n \<and> i<?n \<and> j\<noteq>i \<and> fst(scheme!j)=fst(scheme!i)"
                using hi hj hne hlab by (by100 auto)
              thus ?thesis using hswap by auto
            qed
            thus ?thesis using hp by (by100 simp)
          qed
          thus ?thesis by (by100 auto)
        next
          assume "p \<in> Id"
          thus ?thesis by (by100 auto)
        qed
      qed
      from rtrancl_mono[OF this]
      show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Step 7: Conclude.\<close>
    show "(k, l) \<in> ?S\<^sup>*" using hkl_R \<open>?R\<^sup>* \<subseteq> ?S\<^sup>*\<close> by (by100 blast)
  qed
qed


\<comment> \<open>Transfer quotient\\_of\\_scheme\\_on along a homeomorphism (expert audit 24 §6).
   If Y is a quotient of scheme s, and Y \\<cong> Y', then Y' is also a quotient of s.
   Proof: define q' = h \\<circ> q: P \\<to> Y'. All 11 conditions transfer through h.\<close>
lemma scheme_quotient_transfer_along_homeomorphism:
  assumes hq: "top1_quotient_of_scheme_on Y TY s"
      and hh: "top1_homeomorphism_on Y TY Y' TY' h"
      and htopo_strict': "is_topology_on_strict Y' TY'"
  shows "top1_quotient_of_scheme_on Y' TY' s"
proof -
  let ?n = "length s"
  let ?TP = "\<lambda>S. subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
  \<comment> \<open>Extract quotient witness from Y.\<close>
  from hq obtain P q vx vy where
      hC1: "top1_is_polygonal_region_on P ?n"
    and hC2: "top1_quotient_map_on P (?TP P) Y TY q"
    and hC3: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)"
    and hC4: "\<forall>i<?n. (vx i, vy i) \<in> P"
    and hC5: "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<?n. coeffs i \<ge> 0) \<and> (\<Sum>i<?n. coeffs i) = 1
                   \<and> x = (\<Sum>i<?n. coeffs i * vx i) \<and> y = (\<Sum>i<?n. coeffs i * vy i)}"
    and hC6: "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> Suc i mod ?n \<noteq> j \<longrightarrow> i \<noteq> Suc j mod ?n \<longrightarrow>
        (\<forall>s'\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
           ((1-s') * vx i + s' * vx (Suc i mod ?n), (1-s') * vy i + s' * vy (Suc i mod ?n))
         \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n), (1-t) * vy j + t * vy (Suc j mod ?n)))"
    and hC7: "\<forall>i<?n. \<forall>j<?n. fst (s!i) = fst (s!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
         = (if snd(s!i) = snd(s!j)
            then q ((1-t)*vx j+t*vx(Suc j mod ?n),(1-t)*vy j+t*vy(Suc j mod ?n))
            else q (t*vx j+(1-t)*vx(Suc j mod ?n),t*vy j+(1-t)*vy(Suc j mod ?n))))"
    and hC8: "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n)))
           \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')"
    and hC9: "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s'\<in>{0<..<(1::real)}.
          q ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
        = q ((1-s')*vx j+s'*vx(Suc j mod ?n),(1-s')*vy j+s'*vy(Suc j mod ?n))
        \<longrightarrow> (i=j \<and> t=s') \<or> (fst(s!i)=fst(s!j) \<and> (if snd(s!i)=snd(s!j) then s'=t else s'=1-t))"
    and hC10: "\<forall>i<?n. let cx=(\<Sum>j<?n. vx j)/real ?n; cy=(\<Sum>j<?n. vy j)/real ?n
         in (vx i-cx)*(vy(Suc i mod ?n)-cy)-(vy i-cy)*(vx(Suc i mod ?n)-cx) > 0"
    and hC11: "\<forall>i<?n. \<forall>k<?n. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod ?n \<longrightarrow>
          (vx k-vx i)*(vy(Suc i mod ?n)-vy i)-(vy k-vy i)*(vx(Suc i mod ?n)-vx i) < 0"
    by (rule quotient_of_scheme_extract_vx)
  \<comment> \<open>Define q' = h \\<circ> q: P \\<to> Y'.\<close>
  define q' where "q' = h \<circ> q"
  \<comment> \<open>Topology of Y'.\<close>
  have htopo': "is_topology_on_strict Y' TY'" using htopo_strict' .
  \<comment> \<open>C2': q' = h \\<circ> q is a quotient map from P to Y' (composition of quotient + homeomorphism).\<close>
  have hh_quot: "top1_quotient_map_on Y TY Y' TY' h"
    by (rule top1_homeomorphism_on_imp_quotient_map_on[OF hh])
  have hC2': "top1_quotient_map_on P (?TP P) Y' TY' q'"
    unfolding q'_def by (rule top1_quotient_map_on_comp[OF hC2 hh_quot])
  \<comment> \<open>C7': h preserves equality, so q'(e1) = q'(e2) iff q(e1) = q(e2).\<close>
  have hC7': "\<forall>i<?n. \<forall>j<?n. fst (s!i) = fst (s!j) \<longrightarrow>
      (\<forall>t\<in>I_set. q' ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
       = (if snd(s!i) = snd(s!j)
          then q' ((1-t)*vx j+t*vx(Suc j mod ?n),(1-t)*vy j+t*vy(Suc j mod ?n))
          else q' (t*vx j+(1-t)*vx(Suc j mod ?n),t*vy j+(1-t)*vy(Suc j mod ?n))))"
  proof (intro allI impI ballI)
    fix i j t assume hi: "i < ?n" and hj: "j < ?n" and hlabel: "fst(s!i) = fst(s!j)" and ht: "t \<in> I_set"
    from hC7[rule_format, OF hi hj hlabel ht]
    have hq_eq: "q ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
         = (if snd(s!i) = snd(s!j)
            then q ((1-t)*vx j+t*vx(Suc j mod ?n),(1-t)*vy j+t*vy(Suc j mod ?n))
            else q (t*vx j+(1-t)*vx(Suc j mod ?n),t*vy j+(1-t)*vy(Suc j mod ?n)))" .
    \<comment> \<open>Apply h to both sides.\<close>
    show "q' ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
       = (if snd(s!i) = snd(s!j)
          then q' ((1-t)*vx j+t*vx(Suc j mod ?n),(1-t)*vy j+t*vy(Suc j mod ?n))
          else q' (t*vx j+(1-t)*vx(Suc j mod ?n),t*vy j+(1-t)*vy(Suc j mod ?n)))"
      unfolding q'_def comp_def using hq_eq by (by100 presburger)
  qed
  \<comment> \<open>h is injective on Y (from homeomorphism = bijection).\<close>
  have h_inj: "inj_on h Y"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  \<comment> \<open>q maps P to Y (from quotient map).\<close>
  have q_range: "\<forall>p\<in>P. q p \<in> Y"
    using hC2 unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
  \<comment> \<open>C8': h \\<circ> q injective on interior (h injective + q injective).\<close>
  have hC8': "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n)))
           \<longrightarrow> (\<forall>p'\<in>P. q' p = q' p' \<longrightarrow> p = p')"
  proof (intro ballI impI allI)
    fix p p' assume hp: "p \<in> P" and hp': "p' \<in> P"
        and hint: "\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))"
        and heq: "q' p = q' p'"
    have hqeq: "q p = q p'"
    proof -
      from heq have "h (q p) = h (q p')" unfolding q'_def comp_def by (by100 simp)
      moreover have "q p \<in> Y" using q_range hp by (by100 blast)
      moreover have "q p' \<in> Y" using q_range hp' by (by100 blast)
      ultimately show ?thesis using h_inj unfolding inj_on_def by (by100 blast)
    qed
    show "p = p'" using hC8 hp hint hp' hqeq by (by100 blast)
  qed
  \<comment> \<open>C9': similarly, h preserves the boundary identification pattern.\<close>
  have hC9': "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s'\<in>{0<..<(1::real)}.
        q' ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
      = q' ((1-s')*vx j+s'*vx(Suc j mod ?n),(1-s')*vy j+s'*vy(Suc j mod ?n))
      \<longrightarrow> (i=j \<and> t=s') \<or> (fst(s!i)=fst(s!j) \<and> (if snd(s!i)=snd(s!j) then s'=t else s'=1-t))"
  proof (intro allI impI ballI)
    fix i j t s' assume hi: "i < ?n" and hj: "j < ?n"
      and ht: "t \<in> {0<..<(1::real)}" and hs: "s' \<in> {0<..<(1::real)}"
      and heq: "q' ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
        = q' ((1-s')*vx j+s'*vx(Suc j mod ?n),(1-s')*vy j+s'*vy(Suc j mod ?n))"
    \<comment> \<open>h(q(e1)) = h(q(e2)). Since h injective on Y and both q(e1), q(e2) \\<in> Y: q(e1) = q(e2).\<close>
    have "q ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
        = q ((1-s')*vx j+s'*vx(Suc j mod ?n),(1-s')*vy j+s'*vy(Suc j mod ?n))"
    proof -
      from heq have "h (q ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n)))
          = h (q ((1-s')*vx j+s'*vx(Suc j mod ?n),(1-s')*vy j+s'*vy(Suc j mod ?n)))"
        unfolding q'_def comp_def by (by100 simp)
      moreover have "((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n)) \<in> P"
      proof -
        have hn3: "?n \<ge> 3" using hC1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
        have hn_pos: "0 < ?n" using hn3 by (by100 linarith)
        have hSi: "Suc i mod ?n < ?n" by (rule mod_less_divisor[OF hn_pos])
        define coeffs :: "nat \<Rightarrow> real" where "coeffs k = (if k = i then 1-t else if k = Suc i mod ?n then t else 0)" for k
        have hineq: "i \<noteq> Suc i mod ?n"
        proof (cases "Suc i < ?n")
          case True thus ?thesis by (by100 simp)
        next
          case False hence "Suc i = ?n" using hi by (by100 linarith)
          hence "Suc i mod ?n = 0" by (by100 simp)
          moreover have "i \<ge> 2" using hn3 \<open>Suc i = ?n\<close> by (by100 linarith)
          ultimately show ?thesis by (by100 linarith)
        qed
        have "(\<forall>k<?n. coeffs k \<ge> 0)"
          unfolding coeffs_def using ht by (by100 auto)
        moreover have "(\<Sum>k<?n. coeffs k) = 1"
        proof -
          have "{..<?n} = {i, Suc i mod ?n} \<union> ({..<?n} - {i, Suc i mod ?n})" using hi hSi by (by100 blast)
          have "(\<Sum>k\<in>{..<?n} - {i, Suc i mod ?n}. coeffs k) = 0"
            by (rule sum.neutral) (use coeffs_def in \<open>by100 simp\<close>)
          have "i \<noteq> Suc i mod ?n"
          proof (cases "Suc i < ?n")
            case True thus ?thesis by (by100 simp)
          next
            case False hence "Suc i = ?n" using hi by (by100 linarith)
            hence "Suc i mod ?n = 0" by (by100 simp)
            moreover have "i \<ge> 2" using hn3 \<open>Suc i = ?n\<close> by (by100 linarith)
            ultimately show ?thesis by (by100 linarith)
          qed
          hence hcoeff_sum: "coeffs i + coeffs (Suc i mod ?n) = 1" unfolding coeffs_def by (by100 simp)
          have "(\<Sum>k<?n. coeffs k) = coeffs i + coeffs (Suc i mod ?n) + (\<Sum>k\<in>{..<?n} - {i, Suc i mod ?n}. coeffs k)"
          proof -
            have hi_in: "i \<in> {..<?n}" using hi by (by100 simp)
            from sum.remove[OF finite_lessThan hi_in, of coeffs]
            have "(\<Sum>k<?n. coeffs k) = coeffs i + (\<Sum>k\<in>{..<?n}-{i}. coeffs k)" by (by100 simp)
            moreover have "Suc i mod ?n \<in> {..<?n} - {i}" using hSi \<open>i \<noteq> Suc i mod ?n\<close> by (by100 simp)
            from sum.remove[OF _ this, of coeffs]
            have "(\<Sum>k\<in>{..<?n}-{i}. coeffs k) = coeffs (Suc i mod ?n) + (\<Sum>k\<in>{..<?n}-{i}-{Suc i mod ?n}. coeffs k)"
              by (by100 simp)
            ultimately have "(\<Sum>k<?n. coeffs k) = coeffs i + coeffs (Suc i mod ?n) + (\<Sum>k\<in>{..<?n}-{i}-{Suc i mod ?n}. coeffs k)"
              by (by100 linarith)
            moreover have "{..<?n}-{i}-{Suc i mod ?n} = {..<?n} - {i, Suc i mod ?n}" by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          qed
          thus ?thesis using hcoeff_sum \<open>(\<Sum>k\<in>{..<?n} - {i, Suc i mod ?n}. coeffs k) = 0\<close> by (by100 linarith)
        qed
        moreover have "(1-t)*vx i+t*vx(Suc i mod ?n) = (\<Sum>k<?n. coeffs k * vx k)"
        proof -
          have hi_in: "i \<in> {..<?n}" using hi by (by100 simp)
          have hSi_in: "Suc i mod ?n \<in> {..<?n} - {i}" using hSi hineq by (by100 simp)
          have hrest_zero: "(\<Sum>k\<in>{..<?n} - {i, Suc i mod ?n}. coeffs k * vx k) = 0"
            by (rule sum.neutral) (use coeffs_def in \<open>by100 simp\<close>)
          have hrest2: "(\<Sum>k\<in>{..<?n}-{i}-{Suc i mod ?n}. coeffs k * vx k) = 0"
          proof -
            have "{..<?n}-{i}-{Suc i mod ?n} = {..<?n} - {i, Suc i mod ?n}" by (by100 blast)
            thus ?thesis using hrest_zero by (by100 simp)
          qed
          from sum.remove[OF finite_lessThan hi_in, of "\<lambda>k. coeffs k * vx k"]
          have hsum1: "(\<Sum>k<?n. coeffs k * vx k) = coeffs i * vx i + (\<Sum>k\<in>{..<?n}-{i}. coeffs k * vx k)"
            by (by100 simp)
          from sum.remove[OF _ hSi_in, of "\<lambda>k. coeffs k * vx k"]
          have hsum2: "(\<Sum>k\<in>{..<?n}-{i}. coeffs k * vx k) = coeffs (Suc i mod ?n) * vx (Suc i mod ?n) + (\<Sum>k\<in>{..<?n}-{i}-{Suc i mod ?n}. coeffs k * vx k)"
            by (by100 simp)
          have "(\<Sum>k<?n. coeffs k * vx k) = coeffs i * vx i + coeffs (Suc i mod ?n) * vx (Suc i mod ?n)"
            using hsum1 hsum2 hrest2 by (by100 linarith)
          moreover have "coeffs i = 1-t" unfolding coeffs_def by (by100 simp)
          moreover have "coeffs (Suc i mod ?n) = t" unfolding coeffs_def using hineq by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        moreover have "(1-t)*vy i+t*vy(Suc i mod ?n) = (\<Sum>k<?n. coeffs k * vy k)"
        proof -
          have hi_in: "i \<in> {..<?n}" using hi by (by100 simp)
          have hSi_in: "Suc i mod ?n \<in> {..<?n} - {i}" using hSi hineq by (by100 simp)
          have hrest_zero: "(\<Sum>k\<in>{..<?n} - {i, Suc i mod ?n}. coeffs k * vy k) = 0"
            by (rule sum.neutral) (use coeffs_def in \<open>by100 simp\<close>)
          have hrest2: "(\<Sum>k\<in>{..<?n}-{i}-{Suc i mod ?n}. coeffs k * vy k) = 0"
          proof -
            have "{..<?n}-{i}-{Suc i mod ?n} = {..<?n} - {i, Suc i mod ?n}" by (by100 blast)
            thus ?thesis using hrest_zero by (by100 simp)
          qed
          from sum.remove[OF finite_lessThan hi_in, of "\<lambda>k. coeffs k * vy k"]
          have hsum1: "(\<Sum>k<?n. coeffs k * vy k) = coeffs i * vy i + (\<Sum>k\<in>{..<?n}-{i}. coeffs k * vy k)"
            by (by100 simp)
          from sum.remove[OF _ hSi_in, of "\<lambda>k. coeffs k * vy k"]
          have hsum2: "(\<Sum>k\<in>{..<?n}-{i}. coeffs k * vy k) = coeffs (Suc i mod ?n) * vy (Suc i mod ?n) + (\<Sum>k\<in>{..<?n}-{i}-{Suc i mod ?n}. coeffs k * vy k)"
            by (by100 simp)
          have "(\<Sum>k<?n. coeffs k * vy k) = coeffs i * vy i + coeffs (Suc i mod ?n) * vy (Suc i mod ?n)"
            using hsum1 hsum2 hrest2 by (by100 linarith)
          moreover have "coeffs i = 1-t" unfolding coeffs_def by (by100 simp)
          moreover have "coeffs (Suc i mod ?n) = t" unfolding coeffs_def using hineq by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        ultimately show ?thesis unfolding hC5 by (by100 blast)
      qed
      hence "q ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n)) \<in> Y"
        using q_range by (by100 blast)
      moreover have "((1-s')*vx j+s'*vx(Suc j mod ?n),(1-s')*vy j+s'*vy(Suc j mod ?n)) \<in> P"
      proof -
        have hn3_j: "?n \<ge> 3" using hC1 unfolding top1_is_polygonal_region_on_def by (by100 blast)
        have hn_pos_j: "0 < ?n" using hn3_j by (by100 linarith)
        have hSj: "Suc j mod ?n < ?n" by (rule mod_less_divisor[OF hn_pos_j])
        have hineq_j: "j \<noteq> Suc j mod ?n"
        proof (cases "Suc j < ?n")
          case True thus ?thesis by (by100 simp)
        next
          case False hence "Suc j = ?n" using hj by (by100 linarith)
          hence "Suc j mod ?n = 0" by (by100 simp)
          moreover have "j \<ge> 2" using hn3_j \<open>Suc j = ?n\<close> by (by100 linarith)
          ultimately show ?thesis by (by100 linarith)
        qed
        define cj :: "nat \<Rightarrow> real" where "cj k = (if k = j then 1-s' else if k = Suc j mod ?n then s' else 0)" for k
        have hcj_nn: "\<forall>k<?n. cj k \<ge> 0"
          unfolding cj_def using hs by (by100 auto)
        moreover have hcj_sum: "(\<Sum>k<?n. cj k) = 1"
        proof -
          have "(\<Sum>k\<in>{..<?n} - {j, Suc j mod ?n}. cj k) = 0"
            by (rule sum.neutral) (use cj_def in \<open>by100 simp\<close>)
          have hpair: "cj j + cj (Suc j mod ?n) = 1" unfolding cj_def using hineq_j by (by100 simp)
          have hj_in: "j \<in> {..<?n}" using hj by (by100 simp)
          have hSj_in: "Suc j mod ?n \<in> {..<?n} - {j}" using hSj hineq_j by (by100 simp)
          from sum.remove[OF finite_lessThan hj_in, of cj]
          have "(\<Sum>k<?n. cj k) = cj j + (\<Sum>k\<in>{..<?n}-{j}. cj k)" by (by100 simp)
          moreover from sum.remove[OF _ hSj_in, of cj]
          have "(\<Sum>k\<in>{..<?n}-{j}. cj k) = cj (Suc j mod ?n) + (\<Sum>k\<in>{..<?n}-{j}-{Suc j mod ?n}. cj k)"
            by (by100 simp)
          ultimately have "(\<Sum>k<?n. cj k) = cj j + cj (Suc j mod ?n) + (\<Sum>k\<in>{..<?n}-{j}-{Suc j mod ?n}. cj k)"
            by (by100 linarith)
          moreover have "{..<?n}-{j}-{Suc j mod ?n} = {..<?n} - {j, Suc j mod ?n}" by (by100 blast)
          ultimately have "(\<Sum>k<?n. cj k) = cj j + cj (Suc j mod ?n) + (\<Sum>k\<in>{..<?n} - {j, Suc j mod ?n}. cj k)"
            by (by100 simp)
          thus ?thesis using hpair \<open>(\<Sum>k\<in>{..<?n} - {j, Suc j mod ?n}. cj k) = 0\<close> by (by100 linarith)
        qed
        moreover have "(1-s')*vx j+s'*vx(Suc j mod ?n) = (\<Sum>k<?n. cj k * vx k)"
        proof -
          have hj_in: "j \<in> {..<?n}" using hj by (by100 simp)
          have hSj_in: "Suc j mod ?n \<in> {..<?n} - {j}" using hSj hineq_j by (by100 simp)
          have hrest_zero: "(\<Sum>k\<in>{..<?n} - {j, Suc j mod ?n}. cj k * vx k) = 0"
            by (rule sum.neutral) (use cj_def in \<open>by100 simp\<close>)
          have "(\<Sum>k\<in>{..<?n}-{j}-{Suc j mod ?n}. cj k * vx k) = 0"
          proof -
            have "{..<?n}-{j}-{Suc j mod ?n} = {..<?n} - {j, Suc j mod ?n}" by (by100 blast)
            thus ?thesis using hrest_zero by (by100 simp)
          qed
          from sum.remove[OF finite_lessThan hj_in, of "\<lambda>k. cj k * vx k"]
          have s1: "(\<Sum>k<?n. cj k * vx k) = cj j * vx j + (\<Sum>k\<in>{..<?n}-{j}. cj k * vx k)"
            by (by100 simp)
          from sum.remove[OF _ hSj_in, of "\<lambda>k. cj k * vx k"]
          have s2: "(\<Sum>k\<in>{..<?n}-{j}. cj k * vx k) = cj (Suc j mod ?n) * vx (Suc j mod ?n) + (\<Sum>k\<in>{..<?n}-{j}-{Suc j mod ?n}. cj k * vx k)"
            by (by100 simp)
          have "(\<Sum>k<?n. cj k * vx k) = cj j * vx j + cj (Suc j mod ?n) * vx (Suc j mod ?n)"
            using s1 s2 \<open>(\<Sum>k\<in>{..<?n}-{j}-{Suc j mod ?n}. cj k * vx k) = 0\<close> by (by100 linarith)
          moreover have "cj j = 1-s'" unfolding cj_def by (by100 simp)
          moreover have "cj (Suc j mod ?n) = s'" unfolding cj_def using hineq_j by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        moreover have "(1-s')*vy j+s'*vy(Suc j mod ?n) = (\<Sum>k<?n. cj k * vy k)"
        proof -
          have hj_in: "j \<in> {..<?n}" using hj by (by100 simp)
          have hSj_in: "Suc j mod ?n \<in> {..<?n} - {j}" using hSj hineq_j by (by100 simp)
          have hrest_zero: "(\<Sum>k\<in>{..<?n} - {j, Suc j mod ?n}. cj k * vy k) = 0"
            by (rule sum.neutral) (use cj_def in \<open>by100 simp\<close>)
          have "(\<Sum>k\<in>{..<?n}-{j}-{Suc j mod ?n}. cj k * vy k) = 0"
          proof -
            have "{..<?n}-{j}-{Suc j mod ?n} = {..<?n} - {j, Suc j mod ?n}" by (by100 blast)
            thus ?thesis using hrest_zero by (by100 simp)
          qed
          from sum.remove[OF finite_lessThan hj_in, of "\<lambda>k. cj k * vy k"]
          have s1: "(\<Sum>k<?n. cj k * vy k) = cj j * vy j + (\<Sum>k\<in>{..<?n}-{j}. cj k * vy k)"
            by (by100 simp)
          from sum.remove[OF _ hSj_in, of "\<lambda>k. cj k * vy k"]
          have s2: "(\<Sum>k\<in>{..<?n}-{j}. cj k * vy k) = cj (Suc j mod ?n) * vy (Suc j mod ?n) + (\<Sum>k\<in>{..<?n}-{j}-{Suc j mod ?n}. cj k * vy k)"
            by (by100 simp)
          have "(\<Sum>k<?n. cj k * vy k) = cj j * vy j + cj (Suc j mod ?n) * vy (Suc j mod ?n)"
            using s1 s2 \<open>(\<Sum>k\<in>{..<?n}-{j}-{Suc j mod ?n}. cj k * vy k) = 0\<close> by (by100 linarith)
          moreover have "cj j = 1-s'" unfolding cj_def by (by100 simp)
          moreover have "cj (Suc j mod ?n) = s'" unfolding cj_def using hineq_j by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        ultimately show ?thesis unfolding hC5 by (by100 blast)
      qed
      hence "q ((1-s')*vx j+s'*vx(Suc j mod ?n),(1-s')*vy j+s'*vy(Suc j mod ?n)) \<in> Y"
        using q_range by (by100 blast)
      ultimately show ?thesis using h_inj unfolding inj_on_def by (by100 blast)
    qed
    from hC9[rule_format, OF hi hj ht hs this]
    show "(i=j \<and> t=s') \<or> (fst(s!i)=fst(s!j) \<and> (if snd(s!i)=snd(s!j) then s'=t else s'=1-t))" .
  qed
  \<comment> \<open>Assembly.\<close>
  show ?thesis unfolding top1_quotient_of_scheme_on_def
  proof (intro conjI exI)
    show "is_topology_on_strict Y' TY'" using htopo' .
    show "top1_is_polygonal_region_on P ?n" using hC1 .
    show "top1_quotient_map_on P (?TP P) Y' TY' q'" using hC2' .
    show "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j)" using hC3 .
    show "\<forall>i<?n. (vx i, vy i) \<in> P" using hC4 .
    show "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<?n. 0 \<le> coeffs i) \<and> (\<Sum>i<?n. coeffs i) = 1
        \<and> x = (\<Sum>i<?n. coeffs i * vx i) \<and> y = (\<Sum>i<?n. coeffs i * vy i)}" using hC5 by (by100 simp)
    show "\<forall>i<?n. \<forall>j<?n. i \<noteq> j \<longrightarrow> Suc i mod ?n \<noteq> j \<longrightarrow> i \<noteq> Suc j mod ?n \<longrightarrow>
        (\<forall>s'\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
           ((1-s') * vx i + s' * vx (Suc i mod ?n), (1-s') * vy i + s' * vy (Suc i mod ?n))
         \<noteq> ((1-t) * vx j + t * vx (Suc j mod ?n), (1-t) * vy j + t * vy (Suc j mod ?n)))"
      using hC6 .
    show "\<forall>i<?n. \<forall>j<?n. fst (s!i) = fst (s!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q' ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
         = (if snd(s!i) = snd(s!j)
            then q' ((1-t)*vx j+t*vx(Suc j mod ?n),(1-t)*vy j+t*vy(Suc j mod ?n))
            else q' (t*vx j+(1-t)*vx(Suc j mod ?n),t*vy j+(1-t)*vy(Suc j mod ?n))))"
      using hC7' .
    show "\<forall>p\<in>P. (\<forall>i<?n. \<forall>t\<in>I_set.
              p \<noteq> ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n)))
           \<longrightarrow> (\<forall>p'\<in>P. q' p = q' p' \<longrightarrow> p = p')" using hC8' .
    show "\<forall>i<?n. \<forall>j<?n. \<forall>t\<in>{0<..<(1::real)}. \<forall>s'\<in>{0<..<(1::real)}.
        q' ((1-t)*vx i+t*vx(Suc i mod ?n),(1-t)*vy i+t*vy(Suc i mod ?n))
      = q' ((1-s')*vx j+s'*vx(Suc j mod ?n),(1-s')*vy j+s'*vy(Suc j mod ?n))
      \<longrightarrow> (i=j \<and> t=s') \<or> (fst(s!i)=fst(s!j) \<and> (if snd(s!i)=snd(s!j) then s'=t else s'=1-t))"
      using hC9' .
    show "\<forall>i<?n. let cx=(\<Sum>j<?n. vx j)/real ?n; cy=(\<Sum>j<?n. vy j)/real ?n
         in (vx i-cx)*(vy(Suc i mod ?n)-cy)-(vy i-cy)*(vx(Suc i mod ?n)-cx) > 0" using hC10 .
    show "\<forall>i<?n. \<forall>k<?n. k\<noteq>i \<longrightarrow> k\<noteq>Suc i mod ?n \<longrightarrow>
          (vx k-vx i)*(vy(Suc i mod ?n)-vy i)-(vy k-vy i)*(vx(Suc i mod ?n)-vx i) < 0" using hC11 .
  qed
qed

\<comment> \<open>Strengthened version: canonical quotient has vertex-edge separation.
   In the canonical construction (regular polygon + 3-branch q), a vertex q-value is always
   a vertex (vx(vtgt k), vy(vtgt k)), and an edge-interior q-value is always an edge interior.
   By edge\\_interior\\_not\\_vertex, these are disjoint. So q(vertex) \\<noteq> q(edge\\_interior).\<close>
lemma scheme_quotient_exists_with_vertex_separation:
  fixes scheme :: "(nat \<times> bool) list"
  assumes "length scheme \<ge> 3"
      and hproper: "\<forall>label. card {i. i < length scheme \<and> fst (scheme ! i) = label} \<in> {0, 2}"
  shows "\<exists>(Y :: (real \<times> real) set) (TY :: (real \<times> real) set set)
    (P :: (real \<times> real) set) q (vx :: nat \<Rightarrow> real) (vy :: nat \<Rightarrow> real).
    top1_quotient_of_scheme_on Y TY scheme
    \<and> top1_is_polygonal_region_on P (length scheme)
    \<and> top1_quotient_map_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) Y TY q
    \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
    \<and> (\<forall>k<length scheme. \<forall>j<length scheme. \<forall>s\<in>{0<..<(1::real)}.
        q (vx k, vy k) \<noteq> q ((1-s)*vx j + s*vx(Suc j mod length scheme),
                               (1-s)*vy j + s*vy(Suc j mod length scheme)))"
proof -
  from scheme_quotient_exists(2)[OF assms]
  show ?thesis by (elim exE conjE) (rule exI, rule exI, rule exI, rule exI, rule exI, rule exI,
    intro conjI, assumption+)
qed
end
