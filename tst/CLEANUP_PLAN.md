# Cleanup Plan: Merge AlgIsoFixed back, cache, clean up AlgTop

## Background

AlgIsoFixed.thy was "chunked out" from AlgTop.thy to fix/prove Lemma 65.1
and Theorem 65.2 in isolation (faster builds, no by100 timeouts).
AlgIsoFixedBase.thy contains helper lemmas also chunked out from AlgTop.thy.

Both AlgIsoFixed.thy and AlgIsoFixedBase.thy now have 0 sorrys and pass
thm_oracles (after the pi1_iso_Z_proved fix). The "_fixed" versions are
the canonical proved versions.

AlgTop.thy still has its OWN copies of the same theorems (Lemma_65_1,
Theorem_65_2, K4_nonadjacent, etc.) which are NOT "_fixed" and which
transitively depend on the sorry'd pi1_S2_minus_two_points_iso_Z from
AlgTop0.thy.

## Goal

Make the proved versions official, cache them, and remove/replace the
broken versions in AlgTop.thy.

## Current Layout

```
AlgTop0 (has sorry'd pi1_iso_Z)
  → AlgTopC/AlgTopCached (has proved pi1_iso_Z_proved, + lots of infrastructure)
    → AlgIsoFixedBase (helpers, 0 sorrys, ~5000 lines)
      → AlgIsoFixed (65.1 + 65.2 proved, 0 sorrys, ~10400 lines)
    → AlgTop (has own copies of 65.1/65.2 that use sorry'd pi1_iso_Z)
```

## What AlgTop.thy duplicates from AlgIsoFixed

AlgTop.thy lines 19-6367 contain ~6300 lines that overlap with
AlgIsoFixedBase + AlgIsoFixed:

| AlgTop.thy | AlgIsoFixed* | Lines in AlgTop |
|-----------|-------------|----------------|
| Theorem_63_1_b_generation | AlgIsoFixedBase | 19-768 (750 lines) |
| SCC_pi1_iso_Z | AlgIsoFixedBase | 2219-2326 (107 lines) |
| K4_final_contradiction | AlgIsoFixedBase | 2332-2367 (35 lines) |
| K4_nonadjacent_edges_different_components | AlgIsoFixedBase | 2448-3917 (1469 lines) |
| Lemma_65_1 | AlgIsoFixed (as _fixed) | 3925-6267 (2342 lines) |
| Theorem_65_2 | AlgIsoFixed (as _fixed) | 6270-6367 (97 lines) |

Total duplicated: ~4800 lines in AlgTop.thy

## Proposed Plan

### Step 1: Make AlgTop import AlgIsoFixed instead of AlgTopC

Change ROOT:
```
session AlgTop = AlgIsoFixed +    (was: AlgTopC +)
```

This gives AlgTop access to all AlgIsoFixed theorems. AlgTop already
transitively gets AlgTopC through AlgIsoFixed.

Cost: AlgTop build now waits for AlgIsoFixed (~30s extra).

### Step 2: In AlgTop.thy, replace duplicated theorems with references

Replace the ~4800 lines of duplicated proofs with thin wrappers or
direct `lemmas` declarations:

```isabelle
lemmas Lemma_65_1 = Lemma_65_1_fixed
lemmas Theorem_65_2 = Theorem_65_2_fixed
lemmas K4_nonadjacent_edges_different_components = ...  (from AlgIsoFixedBase)
(etc.)
```

Or just rename the _fixed versions to drop the suffix, if nothing else
in AlgIsoFixed uses the old names.

Also replace `pi1_S2_minus_two_points_iso_Z` with
`pi1_S2_minus_two_points_iso_Z_proved` at line 6347.

### Step 3: Move AlgIsoFixedBase into the cached layer

Since AlgIsoFixedBase has 0 sorrys and passes thm_oracles, it's safe
to cache. Either:
- Merge it into AlgTopCached (append ~5000 lines), or
- Keep it as a separate cached session (current setup is fine)

AlgIsoFixed.thy itself could also be cached, but at 10400 lines it
would significantly increase cache rebuild time. Could keep it as a
non-cached session that builds fast (~30s).

### Step 4: Clean up AlgTop0.thy

- Remove the dead (* ... *) proof skeleton (lines 4023-4191)
- The sorry at line 4019 stays (can't be fixed at this level), but
  document clearly that pi1_iso_Z_proved in AlgTopCached is the
  official version

### Step 5: Clean up naming

Option A (minimal): Keep _fixed names, add `lemmas` aliases in AlgTop.
Option B (clean): Rename _fixed to drop suffix everywhere. This is a
  larger edit but gives cleaner names.

Recommendation: Option A first, Option B later if needed.

### Step 6: Verify

1. `isabelle build -D .` (full rebuild)
2. thm_oracles on: Lemma_65_1, Theorem_65_2, pi1_iso_Z_proved
3. Regenerate indexes

## Risks

- Changing AlgTop's import from AlgTopC to AlgIsoFixed could break
  things if AlgTop uses lemma names that clash with AlgIsoFixed names.
  Need to check for name clashes.

- Deleting ~4800 lines from AlgTop.thy could break downstream references
  (other files that import AlgTop and use these lemma names). But
  currently nothing imports AlgTop.

- The `lemmas X = X_fixed` aliases should preserve backward compatibility.

## Estimated Work

- Step 1: 1 line edit in ROOT
- Step 2: Replace ~4800 lines with ~20 lines of aliases. Medium risk.
- Step 3: No change needed (already cached as separate session)
- Step 4: Delete ~170 lines of dead code
- Step 5: ~10 line edits
- Step 6: ~20 min rebuild + verification
