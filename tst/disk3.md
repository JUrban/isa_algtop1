# disk3.md — Final implementation plan (angle-based boundary map)

## Current state

`polygon_homeomorphic_to_disk_with_boundary` has **5 sorrys** in the proof body
(plus 1 sorry at the call site for hvert_hp):

1. **hpsi_agree** (L3521): overlap agreement of local maps on shared edges
2. **h\<psi>_cont** (L3539): continuity of ψ on P
3. **h\<psi>_surj** (L3544): ψ ` P = top1_B2
4. **h\<psi>_inj** (L3549): inj_on ψ P
5. **h\<psi>_bd** (L3600): ψ ` BdP = top1_S1

Already proved:
- Di > 0 from CCW (hDi_pos)
- Cramer coordinates beta_cr, gamma_cr (explicit, no SOME)
- Cramer reconstruction: z - c = β'*(v_i - c) + γ'*(v_{i+1} - c)
- β' ≥ 0, γ' ≥ 0 (from sign change)
- β' + γ' ≤ 1 (from hvert_hp edge-side assumption)
- hP_cones: every z ∈ P is in some cone (~200 lines)
- psi_local definition (normalized chord approach)
- Centroid maps to origin

## Key change: angle-based boundary map

Replace the current `psi_local` which uses normalized chord:
```isabelle
psi_local i z = let b = beta_cr i z; g = gamma_cr i z;
    wx = b * qx i + g * qx(i+1); wy = b * qy i + g * qy(i+1);
    r = sqrt(wx² + wy²)
in if r = 0 then (0,0) else ((b+g) * wx/r, (b+g) * wy/r)
```

With angle-based:
```isabelle
psi_local i z = let b = beta_cr i z; g = gamma_cr i z;
    s = b + g;
    u = (if s = 0 then 0 else g / s);
    θ = 2 * pi * (real i + u) / real n
in (s * cos θ, s * sin θ)
```

Advantages:
- **No normalization** — cos/sin are already on S¹
- **Surjectivity trivial** — angle covers [0, 2π) as i and u vary
- **Injectivity trivial** — (s, θ) = polar coordinates, s ∈ [0,1], θ determines sector+param
- **Continuity at centroid** — s → 0 implies ψ → (0,0) regardless of θ
- **No "chord ≠ 0" proof needed**

Disadvantages:
- cos/sin make algebraic simplification harder than polynomial arithmetic
- Need cos/sin continuity lemmas (available in Complex_Main)

## Plan

### Step 0: Change psi_local definition (~10 lines)

Replace the normalized-chord psi_local with the angle-based version.
Also change qx/qy references if needed (they may still be useful as
target vertex coordinates, but the map no longer interpolates between them).

### Step 1: Overlap agreement (~30 lines)

On the shared edge between cone i and cone i+1 (ray from c through v_{i+1}):
- In cone i: β_i = 0, γ_i = s, so u_i = γ_i/s = 1. θ_i = 2π(i+1)/n.
- In cone i+1: β_{i+1} = s, γ_{i+1} = 0, so u_{i+1} = 0. θ_{i+1} = 2π(i+1)/n.
- Same angle! So psi_local i z = psi_local (i+1) z = (s·cos θ, s·sin θ). ✓

At centroid c: s = 0 for all cones, so psi_local i c = (0,0) for all i. ✓

For non-adjacent cones: overlap is {c} only (from strict CCW + convexity),
so agreement at c suffices.

### Step 2: Continuity (~50 lines)

Each psi_local i is continuous on C_i:
- beta_cr i z and gamma_cr i z are polynomial in z (rational with fixed
  denominator Di > 0). Hence continuous.
- s = beta_cr + gamma_cr: continuous (sum of continuous).
- u = gamma_cr / s: continuous where s > 0.
- θ = 2π(i + u)/n: continuous where u is continuous.
- cos θ, sin θ: continuous (from continuous_on_cos, continuous_on_sin).
- s · cos θ, s · sin θ: continuous (product of continuous).

At centroid (s = 0): psi_local i (cx,cy) = (0,0).
For continuity at c: |psi_local i z| = s = beta_cr + gamma_cr.
As z → c: beta_cr → 0 and gamma_cr → 0 (from Cramer, z-c → 0 with Di > 0).
So s → 0, hence psi_local → (0,0). ✓

Handle: u = γ/s is undefined when s = 0, but psi_local is defined as (0,0)
in that case. Need to show continuity of the WHOLE expression including
the s=0 branch. Use: |psi_local i z| = s → 0, so the limit is (0,0)
regardless of the angle. This is a squeeze argument.

Then: pasting lemma for finite closed cover {C_i | i < n}.
Each C_i is closed (compact convex hull of 3 points → closed in R²).
∪ C_i = P (from hP_cones).
Continuous on each + agree on overlaps → continuous on P.

Use `continuous_on_closed_Un` for 2 sets, then iterate for n sets.
Or prove a finite-union pasting lemma if not available.

### Step 3: Surjectivity (~30 lines)

For y ∈ B²:
- If y = (0,0): ψ(c) = (0,0). c ∈ P. ✓
- If y = (r·cos φ, r·sin φ) with 0 < r ≤ 1:
  Find i such that 2πi/n ≤ φ < 2π(i+1)/n (sector containing angle φ).
  Set u = (φ·n/(2π)) - i (so 0 ≤ u < 1 for interior, u could be 0 or 1 at edges).
  Then θ = 2π(i+u)/n = φ. ✓
  Set s = r, so β = s·(1-u) = r·(1-u), γ = s·u = r·u, α = 1-s = 1-r.
  Then z = α·c + β·v_i + γ·v_{i+1} ∈ P (convex combination, all ≥ 0, sum = 1).
  And psi_local i z = (s·cos θ, s·sin θ) = (r·cos φ, r·sin φ) = y. ✓

Key: need β+γ = r ≤ 1, β ≥ 0, γ ≥ 0. All hold since r ∈ (0,1], u ∈ [0,1].

### Step 4: Injectivity (~40 lines)

If ψ(z₁) = ψ(z₂):
- Case both = (0,0): s₁ = s₂ = 0, so α₁ = α₂ = 1.
  z₁ = 1·c + 0·v_i + 0·v_{i+1} = c = z₂. ✓
- Case ψ = (r·cos φ, r·sin φ) with r > 0:
  s₁ = |ψ(z₁)| = r = |ψ(z₂)| = s₂. (Since |psi_local i z| = s = β+γ.)
  θ₁ = φ = θ₂ (since cos θ₁ = cos θ₂ and sin θ₁ = sin θ₂, and θ in range).
  From θ₁ = θ₂: same i (sector) and same u (within sector).
  From s₁ = s₂ and u₁ = u₂: β₁ = s·(1-u) = β₂, γ₁ = s·u = γ₂.
  From α = 1-s: α₁ = α₂.
  So z₁ = α·c + β·v_i + γ·v_{i+1} = z₂. ✓

Key subtlety (from reviewer): at sector boundaries (u=0 or u=1), the
angle θ = 2πi/n could be represented in two adjacent cones. But:
- u=0 in cone i gives β=s, γ=0: z = (1-s)·c + s·v_i
- u=1 in cone i-1 gives β=0, γ=s: z = (1-s)·c + s·v_i (same!)
So the z value is the SAME even if the cone index differs. ✓

Formally: need |psi_local i z| = beta_cr i z + gamma_cr i z.
With the angle-based definition: |(s·cos θ, s·sin θ)| = |s| · |(cos θ, sin θ)|
= |s| · 1 = s (since s ≥ 0). ✓

### Step 5: ψ(BdP) = S¹ (~25 lines)

⊆: For x ∈ BdP on edge i at parameter u:
x = (1-u)·v_i + u·v_{i+1}. In cone i: α = 0, β = 1-u, γ = u.
s = β+γ = 1. psi_local i x = (1·cos(2π(i+u)/n), 1·sin(2π(i+u)/n)) ∈ S¹. ✓

⊇: For any (cos φ, sin φ) ∈ S¹:
Find i with 2πi/n ≤ φ < 2π(i+1)/n. Set u = φ·n/(2π) - i.
Set x = (1-u)·v_i + u·v_{i+1} ∈ BdP.
ψ(x) = (cos(2π(i+u)/n), sin(2π(i+u)/n)) = (cos φ, sin φ). ✓

## Verification: |psi_local i z| = s

With the angle definition: psi_local i z = (s·cos θ, s·sin θ).
|(s·cos θ, s·sin θ)|² = s²·cos²θ + s²·sin²θ = s²·(cos²θ + sin²θ) = s².
So |psi_local i z| = s (since s ≥ 0). ✓

This is key for: ψ maps to B² (s ∈ [0,1]), ψ(BdP) ⊆ S¹ (s=1),
and injectivity (s determines radius).

## Verification: psi_local image ⊆ B²

s = β+γ ∈ [0,1] (from β,γ ≥ 0 and β+γ ≤ 1).
|psi_local| = s ≤ 1. So image ⊆ B². ✓

## What needs to change in the existing code

1. Replace `psi_local` definition (line ~3225)
2. Remove qx, qy definitions (lines ~3191-3192) — no longer needed
   (or keep them, they don't hurt)
3. Remove the normalized-chord sorry comments
4. Write proofs for all 5 sorrys

The downstream code (h\<psi>_bij, Theorem_26_6, h\<psi>_int, etc.) is
UNCHANGED — it only uses h\<psi>_cont, h\<psi>_surj, h\<psi>_inj, h\<psi>_bd.

## Estimated effort

| Step | Lines | Difficulty |
|------|-------|-----------|
| 0. Change psi_local | 10 | Easy |
| 1. Overlap agreement | 30 | Medium |
| 2. Continuity | 50 | Medium-Hard |
| 3. Surjectivity | 30 | Easy |
| 4. Injectivity | 40 | Medium |
| 5. ψ(BdP) = S¹ | 25 | Easy |
| **Total** | **~185** | |

The angle-based approach cuts ~200 lines compared to disk2.md by
eliminating ALL target-sector lemmas (no normalization needed).

## Risk assessment

**Low risk**: Steps 0, 3, 5 — direct constructions with cos/sin.
**Medium risk**: Steps 1, 4 — need careful handling of boundary cases.
**Medium-Hard risk**: Step 2 — continuity at centroid needs squeeze
argument, and the pasting lemma for n closed sets needs either a library
lemma or a short induction proof.

**Main risk**: cos/sin computation in Isabelle. Need facts like:
- cos²θ + sin²θ = 1 (available as `sin_cos_squared_add`)
- cos/sin continuous (available as `continuous_on_cos`, `continuous_on_sin`)
- cos/sin injective on [0, 2π) (need angle uniqueness)
- 2π periodicity

These are all in `Complex_Main` which we import.
