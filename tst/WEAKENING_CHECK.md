# Statement Faithfulness Check — 2026-05-05

Cross-check of formalized theorem statements against Munkres algtop.tex.
Files: `ALL_STATEMENTS.txt`, `NAMED_THEOREMS.txt` (full dumps for expert review).

## Weakened Statements (formalization is logically weaker than textbook)

### 1. Theorem 70.1 — SvK universal property: MISSING UNIQUENESS
- **Textbook** (line 3195): "there is a **unique** homomorphism Φ"
- **Formalization** (`Theorem_70_1_universal_property`, AlgTopCached:15854): `∃Φ. ...` (existence only)
- **Impact**: High — uniqueness is used in Theorem 70.2 proof
- **Fix**: `Theorem_70_1_uniqueness` now stated in AlgTop.thy:11 with sorry. Proof via Theorem 59.1.

### 2. Theorem 67.6 — Uniqueness of direct sums: MISSING UNIQUENESS + COMMUTING
- **Textbook** (line 2671): "there is a **unique** isomorphism φ: G→G' such that φ∘iα = iα' for each α"
- **Formalization** (`Theorem_67_6_direct_sum_unique`, AlgTopCached:7402): `top1_groups_isomorphic_on H1 mulH1 H2 mulH2`
- **Impact**: Medium — drops uniqueness and the commuting-with-embeddings condition
- **Note**: The building block `Lemma_67_5` (extension property) DOES include uniqueness. 67.6 follows.

### 3. Theorem 68.4 — Uniqueness of free products: MISSING UNIQUENESS + COMMUTING
- **Textbook** (line 2946): "there is a **unique** isomorphism φ: G→G' such that φ∘iα = iα' for all α"
- **Formalization** (`Theorem_68_4_free_product_unique`, AlgTopCached:12544): `top1_groups_isomorphic_on G1 mul1 G2 mul2`
- **Impact**: Medium — drops uniqueness and commuting condition
- **Note**: `Lemma_68_3_extension_property` (AlgTopCached:11289) DOES include uniqueness.

### 4. Theorem 73.1 — Torus presentation: REPLACED WITH COROLLARY
- **Textbook** (line 3702): "π₁(T) has presentation ⟨α,β | αβα⁻¹β⁻¹⟩"
- **Formalization** (`Theorem_73_1_torus_presentation`, AlgTop:867): `π₁(T) ≅ Z×Z`
- **Impact**: Low — the Z×Z form is the corollary (73.2 in text), logically weaker than the presentation but equivalent for most uses. The presentation form would need Theorem 72.1 (which has sorry).

### 5. Theorem 71.1 — Wedge of circles: GENERATORS NOT IDENTIFIED
- **Textbook** (line 3502): "the loops f₁,...,fₙ represent a system of free generators for π₁(X,p)"
- **Formalization** (`Theorem_71_1_wedge_of_circles_finite`, AlgTop:581): `∃G mul e invg ι. free_group G ι {..<n} ∧ G ≅ π₁(X,p)`
- **Impact**: Low — says π₁ is isomorphic to a free group on n generators, but doesn't identify the generators as circle inclusions. The isomorphism implicitly provides the identification.

### 6. Corollary 70.4 — Simply connected V: NO EXPLICIT QUOTIENT MAP
- **Textbook** (line 3445): "the homomorphism Φ of Theorem 70.1 induces an isomorphism..."
- **Formalization** (`Corollary_70_4_simply_connected_V`, AlgTopCached:27422): states the isomorphism exists but doesn't exhibit it as the Φ from 70.1
- **Impact**: Low — the isomorphism is constructive in the proof, just not named in the conclusion.

## Correctly Stated (verified against textbook)

### Proved theorems matching textbook:
- **Theorem 54.5** (π₁(S¹)≅Z): Correct — `Theorem_54_5` in Top0
- **Theorem 55.6** (Brouwer FPT): Correct
- **Theorem 56.1** (FTA): Correct
- **Theorem 57.2** (no antipode-preserving S²→S¹): Correct
- **Theorem 57.3** (Borsuk-Ulam): Correct
- **Theorem 59.1** (j₁/j₂ generate): Correct — full generation statement
- **Theorem 59.3** (Sⁿ simply connected): Correct
- **Theorem 60.1** (product of groups): Correct
- **Theorem 61.3** (Jordan separation): Correct
- **Theorem 62.3** (invariance of domain): Correct
- **Theorem 63.4** (Jordan curve theorem): Correct
- **Theorem 67.4** (direct sum exists): Correct — includes embeddings and injectivity
- **Theorem 67.8** (rank well-defined): Correct — `∃f. bij_betw f S1 S2`
- **Theorem 68.2** (free product exists): Correct — via `top1_is_free_product_on`
- **Theorem 68.7** (quotient free product): Correct — full statement with N₁∪N₂
- **Theorem 69.2** (free product of free is free): Correct — includes generator tracking
- **Theorem 69.4** (abelianization of free): Correct — includes φ∘ι correspondence
- **Lemma 68.3** (extension property): Correct — **includes uniqueness** ✓
- **Lemma 68.9** (normal closure = conjugates): Correct
- **Lemma 69.3** (commutator in kernel): Correct
- **Theorem 70.2 parameterized**: Correct — full SvK classical statement with FP as parameter
- **Corollary 52.2** (basepoint independence): Correct
- **Lemma 62.1** (homotopy extension): Correct for R² target

### Stated with sorry, statement appears correct:
- **Theorem 65.2**: Correct statement (inclusion iso)
- **Theorem 72.1**: Correct statement (attaching 2-cell kills class)
- **Theorem 74.3**: Correct (n-torus group presentation)
- **Theorem 74.4**: Correct (m-projective plane presentation)
- **Theorem 80.3**: Correct (universal covering factors through any covering)
- **Theorem 82.1**: Correct (existence of covering for any subgroup)
- **Theorem 85.1**: Correct (Nielsen-Schreier)
- **Theorem 85.3**: Correct (Schreier index formula)

## Misstated or Mislabeled

### Mislabeled:
1. `Theorem_83_2` should be `Theorem_83_4` (Munkres numbering)
2. `Lemma_58_5` should be `Lemma_58_4` (AlgTopBase0)
3. `Theorem_80_1` has no matching number (unnumbered result in text)

### Abandoned (`oops`):
1. `Theorem_70_2_SvK` (AlgTopCached:14136) — type variable; parameterized version works
2. `Corollary_70_3` (AlgTopCached:27131) — type variable; no parameterized replacement yet

## Recommendations

1. **Strengthen Theorem 70.1**: prove the uniqueness sorry (straightforward from 59.1)
2. **Strengthen 67.6 and 68.4**: add uniqueness + commuting conditions (building blocks exist)
3. **Add Corollary 70.3 parameterized**: like 70.2/70.4 pattern
4. **State Theorem 73.1 as presentation**: currently only the Z×Z corollary form
5. **Fix numbering**: 83.2→83.4, 58.5→58.4
