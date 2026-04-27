# Plan to finish JCT — 2 remaining sorries in AlgTop_JCT_Base.thy

## Status

17 total sorries in AlgTop_JCT_Base.thy. 2 are on the JCT critical path:
- Line ~3197: `hf_fi` (Theorem 51.3 reparametrization)
- Line ~3204: `hfi_gi` (telescoping computation)

Both are in Theorem_59_1 Step 2. All other Step 1/Step 2 infrastructure is proved.

## Chain: JCT → Theorem_63_5 → Theorem_61_4 → Theorem_59_1

## Sorry 1: `hf_fi` — Theorem 51.3 (reparametrization)

### Statement
```
f ≃ foldr top1_path_product (map fi [0..<m]) (top1_constant_path x0)
```
where `fi i t = f(subdivision i + t * (subdivision(Suc i) - subdivision i))`.

### Textbook (algtop.tex line 321)
> Theorem 51.3. Let f be a path in X, and let a0,...,an be numbers such that
> 0=a0 < a1 < ... < an = 1. Let fi be the positive linear map of I onto
> [a_{i-1}, a_i] followed by f. Then [f] = [f1]*...*[fn].

### Proof approach: induction on m
- **Base m=1**: fi(0)(t) = f(0 + t*(1-0)) = f(t) = f. So foldr = f*const.
  Need: f ≃ f*const. Use `Theorem_51_2_right_identity` (backward direction).
  Actually: `Theorem_51_2_right_identity` gives `f*const ≃ f`, and we need
  `f ≃ f*const`, so use `Lemma_51_1_path_homotopic_sym`.
  
- **Step m → m+1**: Write f as the path product of
  "f restricted to [0, sub(m)]" and "f restricted to [sub(m), 1]".
  The first part ≃ f1*...*fm by IH. The second part = f(m+1).
  So f ≃ (f1*...*fm) * f(m+1) = f1*...*fm*f(m+1).
  
  The key fact: `f ≃ f_left * f_right` where f_left(t) = f(t * sub(m)/1)
  and f_right(t) = f(sub(m) + t*(1-sub(m))). This is the path product
  definition: top1_path_product applied to the two halves of f.
  
  Formally: `f ≃ top1_path_product f_left f_right` via a reparametrization
  homotopy H(s,t) that stretches/compresses the parameter.

### Key lemmas needed
- `Theorem_51_2_right_identity`: f*const ≃ f
- `Lemma_51_1_path_homotopic_sym`: symmetry of path homotopy
- `Lemma_51_1_path_homotopic_trans`: transitivity
- `path_homotopic_product_left/right`: product respects homotopy
- Reparametrization homotopy for the induction step (the hard part)

### Alternative: prove for m=2 via explicit homotopy, then induct
For m=2 with subdivision 0 < a < 1:
- f(t) for t ∈ [0,1]
- f1(t) = f(t*a) for t ∈ [0,1] — maps to [0,a]
- f2(t) = f(a + t*(1-a)) for t ∈ [0,1] — maps to [a,1]
- top1_path_product f1 f2 (t) = f1(2t) for t ≤ 1/2, f2(2t-1) for t > 1/2
  = f(2t*a) for t ≤ 1/2, f(a + (2t-1)*(1-a)) for t > 1/2

Need: f ≃ top1_path_product f1 f2 via H(s,t) = f(φ_s(t)) where
φ_s is a piecewise linear reparametrization of [0,1] that at s=0 is
the identity (giving f) and at s=1 is the path-product reparametrization
(giving f1*f2).

This is Munkres' proof of Theorem 51.2 associativity, adapted.

## Sorry 2: `hfi_gi` — telescoping computation

### Statement
```
foldr top1_path_product fi_list (top1_constant_path x0)
  ≃ foldr top1_path_product gs_list (top1_constant_path x0)
```
where `gi i = (αs' i * fi i) * rev(αs'(Suc i))`, `αs'(0) = αs'(m) = const_x0`.

### Textbook (algtop.tex line 1569)
> Direct computation shows that [g1]*[g2]*...*[gn] = [f1]*[f2]*...*[fn].

### Proof: step-by-step path algebra

The "direct computation" in π₁ is:
```
[g1]*...*[gn]
= [(α0*f1)*rev(α1)] * [(α1*f2)*rev(α2)] * ... * [(α(n-1)*fn)*rev(αn)]
```

By associativity of path product in π₁(X, x0):
```
= [α0] * [f1] * [rev(α1)] * [α1] * [f2] * [rev(α2)] * ... * [fn] * [rev(αn)]
```

By inverse law [rev(αk)] * [αk] = [const]:
```
= [α0] * [f1] * [const] * [f2] * [const] * ... * [fn] * [rev(αn)]
```

By identity law [const] * [x] = [x]:
```
= [α0] * [f1] * [f2] * ... * [fn] * [rev(αn)]
```

Since α0 = αn = const_x0:
```
= [const] * [f1] * ... * [fn] * [rev(const)]
= [const] * [f1] * ... * [fn] * [const]
= [f1] * ... * [fn]
```

### Formal proof structure

Each step is a `Lemma_51_1_path_homotopic_trans` application:

1. Expand gi definitions in the foldr product
2. Apply `Theorem_51_2_associativity` to reassociate (flatten the binary tree)
3. Apply `Theorem_51_2_invgerse_right` at each rev(αk)*αk pair
4. Apply `Theorem_51_2_left_identity` to remove each [const]
5. Apply `h\<alpha>s'_0` and `h\<alpha>s'_m` to substitute α0 = αm = const
6. Apply `Theorem_51_2_left_identity` and `Theorem_51_2_right_identity` to clean up

Each step uses `path_homotopic_product_left` or `path_homotopic_product_right`
to apply the homotopy inside a product.

### By induction on m

**Base m=1**:
- gs_list = [g0], fi_list = [f0]
- foldr gs = g0 * const = ((const * f0) * rev(const)) * const
- foldr fi = f0 * const
- Need: ((const * f0) * rev(const)) * const ≃ f0 * const
- Steps: const*f0 ≃ f0 (left id), rev(const) = const,
  (f0 * const) * const ≃ f0 * (const * const) ≃ f0 * const (assoc + left id)

**Step m → m+1**: induction with product-respects-homotopy on the left.

## Estimated effort
- Sorry 1 (Theorem 51.3): ~60-80 lines
- Sorry 2 (telescoping): ~80-100 lines  
- Total: ~150 lines of path algebra

## Available lemmas (in Top1_Ch9_13.thy)
- `Theorem_51_2_associativity`: (f*g)*h ≃ f*(g*h)
- `Theorem_51_2_left_identity`: const*f ≃ f
- `Theorem_51_2_right_identity`: f*const ≃ f  
- `Theorem_51_2_invgerse_left`: f*rev(f) ≃ const
- `Theorem_51_2_invgerse_right`: rev(f)*f ≃ const
- `path_homotopic_product_left`: f≃g → f*h ≃ g*h
- `path_homotopic_product_right`: f≃g → h*f ≃ h*g
- `Lemma_51_1_path_homotopic_trans`: f≃g, g≃h → f≃h
- `Lemma_51_1_path_homotopic_sym`: f≃g → g≃f
- `top1_path_product_is_path`: path * path = path
- `top1_path_reverse_is_path`: path → reverse path
- `top1_constant_path_is_path`: const is path

## Build command
```
/project/bin/isabelle build -D . AlgTopBase
```
(~33s, do NOT rebuild AlgTop during iteration)

## CRITICAL RULES
1. Follow the textbook proof LITERALLY — no shortcuts
2. Sorry-first: write skeleton with sorry, build, then fill in
3. Build only AlgTopBase during iteration
4. Use `thm_oracles` to verify when done
