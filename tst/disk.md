# Polygon-to-Disk Homeomorphism: Analysis and Proposal

## Current State

The lemma `polygon_homeomorphic_to_disk_with_boundary` (AlgTop.thy, line ~2973) claims:
given a convex polygon P with n≥3 vertices in R², there exists a homeomorphism ψ: P → B²
with ψ(BdP) = S¹ and ψ|_{Int P} homeomorphism onto Int B².

**4 sorrys remain**: ψ continuous, ψ surjective, ψ injective, ψ(BdP) = S¹.

The **19 proved steps** downstream (Theorem_26_6 application → homeomorphism,
restriction to interior, etc.) depend only on these 4 properties, not on ψ's definition.
~2000 lines of further infrastructure (Hausdorff, CW data, A=wedge, Thm 72.1)
are also untouched.

## The Problem

ψ is currently defined using Hilbert's SOME operator:
```isabelle
define ψ where "ψ z = (if z = c then (0, 0)
    else let r = (SOME r. r > 0 ∧ c + r*(z-c) ∈ BdP);
             x = c + r*(z-c);
             s = |z-c| / |x-c|
         in (s * fst(h_bd x), s * snd(h_bd x)))"
```

This makes reasoning nearly impossible because:
1. `SOME` gives an arbitrary witness — you can't compute with it
2. To show ψ is continuous, you'd need continuity of `SOME r. ...` as a function of z
3. The uniqueness of the ray-boundary intersection (needed for SOME) is itself non-trivial

## What the Book Says (Munkres §74)

> "If p and q are fixed points of Int P and Int Q, then this homeomorphism
> may be extended to a homeomorphism of P with Q by letting it map **the line
> segment from p to the point x of Bd P linearly onto the line segment from
> q to h(x)**."

The book's formula: **ψ((1-t)·p + t·x) = (1-t)·q + t·h(x)** for x ∈ Bd P, t ∈ [0,1].

With p = centroid, q = (0,0): **ψ((1-t)·c + t·x) = t·h(x)**.

This is a direct parametric formula — no SOME, no ray intersection.

## Proposed Approach

### Step 1: Parametric decomposition of P

Every z ∈ P can be written as z = (1-t)·c + t·x for unique t ∈ [0,1], x ∈ Bd P
(when z ≠ c; for z = c, take t = 0).

The **uniqueness** follows from convexity: the ray from c through z exits P at
exactly one boundary point (since P is convex and bounded, and c is interior).

Key question: **can we define the decomposition (t, x) as a function of z
without SOME?**

For a convex polygon with n edges, the boundary point x lies on some edge i.
The edge index i can be determined by which "sector" z falls in (using the CCW
cross product signs — we already have the CCW condition in the definition).

Concretely: for z ≠ c, the direction z-c determines a unique sector between
consecutive vertices v_i and v_{i+1}. The ray from c through z intersects
edge i at a computable parameter.

### Step 2: Explicit edge-index function

```
sector(z) = (THE i. i < n ∧ cross2(v_i - c, z - c) ≥ 0 ∧ cross2(z - c, v_{i+1} - c) ≥ 0)
```

With the CCW condition (all D_i > 0), exactly one sector contains z-c.
THE (definite description) is better than SOME here because uniqueness is explicit.

### Step 3: Explicit ray-boundary intersection

For z in sector i, the ray from c through z hits edge i at:
```
x = (1-t_edge)·v_i + t_edge·v_{i+1}
```
where t_edge is the solution of the 2×2 linear system (Cramer's rule — we already
have this infrastructure from the old cone decomposition proof!).

### Step 4: Direct ψ definition

```
ψ(z) = if z = c then (0,0)
        else let i = sector(z);
                 t_edge = cramer_param(i, z);
                 x = (1-t_edge)·v_i + t_edge·v_{i+1};
                 s = |z-c| / |x-c|
             in s · h_bd(x)
```

Or even simpler: use the CONE DECOMPOSITION directly. We already proved
(in the old, now-deleted code) that every z ∈ P lies in some cone
z = α·c + β·v_i + γ·v_{i+1}. Then:
- t = β + γ (= 1 - α)  
- x = (β·v_i + γ·v_{i+1}) / (β + γ)
- s = t = 1 - α
- ψ(z) = (1-α) · h_bd(x)

### Step 5: Properties from the construction

With a direct formula:

- **ψ continuous**: each piece (sector detection, Cramer parameter, h_bd, scaling)
  is continuous. On cone boundaries, the pieces agree (same edge parametrization).
  Pasting lemma for finite closed cover → globally continuous.

- **ψ surjective**: for any point s·(cos θ, sin θ) ∈ B², find x ∈ BdP with
  h_bd(x) = (cos θ, sin θ) (h_bd surjective onto S¹), then z = (1-s)·c + s·x ∈ P.

- **ψ injective**: if ψ(z₁) = ψ(z₂), then s₁·h_bd(x₁) = s₂·h_bd(x₂).
  Since h_bd maps to S¹: s₁ = s₂ and h_bd(x₁) = h_bd(x₂).
  h_bd injective (different edges map to different arcs, same edge is linear) → x₁ = x₂.
  Same s and same x → z₁ = z₂.

- **ψ(BdP) = S¹**: for x ∈ BdP, s = 1, so ψ(x) = h_bd(x) ∈ S¹.
  h_bd surjective onto S¹ → ψ(BdP) = S¹.

## Risk Assessment

**What could go wrong:**

1. **Sector detection continuity**: The sector function is discontinuous at
   sector boundaries (rays from c through vertices). But ψ itself is continuous
   across boundaries because adjacent cones agree on shared edges.
   This requires the pasting lemma for finite closed covers.

2. **h_bd surjectivity onto S¹**: The normalized interpolation between regular
   polygon vertices on S¹ must cover ALL of S¹. For n ≥ 3, the regular n-gon
   inscribed in S¹ has edges covering all angles. The normalized interpolation
   of each edge traces an arc of S¹. Union = S¹. This should be provable but
   needs trigonometric calculations.

3. **h_bd injectivity**: Different edges map to different arcs of S¹ (disjoint
   angle ranges). Same edge: the normalized interpolation is monotone in angle
   (for n ≥ 3, each edge subtends < π). This needs some angular analysis.

4. **Cramer parameter well-definedness**: D_i > 0 (from CCW) ensures the 2×2
   system is non-degenerate. We already have this infrastructure.

**What I'm confident about:**

- The pasting lemma approach for continuity is standard and we have
  `pasting_lemma_closed` in the library.
- The Cramer's rule computation was already done in the old cone decomposition
  (deleted but can be recovered from backups).
- Injectivity/surjectivity follow cleanly from the direct formula.

## Effort Estimate

- Redefine ψ with direct formula: ~20 lines (replace SOME with THE/explicit)
- Prove sector existence/uniqueness: ~40 lines (CCW + cross product signs)
- Prove ψ continuous: ~60 lines (pasting lemma on n cones)
- Prove ψ surjective: ~30 lines (h_bd surjective + ray construction)
- Prove ψ injective: ~30 lines (h_bd injective + s uniqueness)
- Prove ψ(BdP) = S¹: ~20 lines (s=1 on boundary + h_bd surjective)

**Total: ~200 lines**, replacing 4 sorrys.

## Alternative: Just sorry it

In quick_and_dirty mode, the 4 sorrys are accepted and everything downstream
works. The homeomorphism ψ: P → B² is a standard result that any mathematician
would accept. The formalization effort (~200 lines) is significant but follows
the book's construction exactly.

The question is whether the 200-line investment is worth it vs leaving as sorrys
and focusing on other parts of the formalization.
