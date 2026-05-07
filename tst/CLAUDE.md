# Rules for Working on AlgTop Formalization of /project/algtop.tex in Isabelle/HOL.

# First pass: a "faithful formal proof sketch pass": for each stated
theorem corresponding to the book, create a compiling proof sketch
(i.e. with sorries) that will faithfully mirror the algtop.tex  proof.

## Note: while it's OK to initially just write the proof in comments (if it's easier),
this pass really has to ultimately produce a nontrivial formal
proof sketch. Just a comment is	not a "faithful formal proof sketch".

## Things below (except the checking instructions) should come only after the formal proof sketch pass is done for all

## ❗ ABSOLUTE RULE: New Proof Workflow

When writing **any new proof code** (skeleton, step, or edit):

1. **Only use `sorry`.**
2. **No exceptions** — do not write:

   * `by ...`, `done`
   * `simp`, `auto`, `blast`, `metis`, `linarith`
   * `rule`, `erule`, `drule`, etc.
3. Write the full proof structure using `sorry`, then **compile immediately**.
4. Only after a successful build:

   * replace `sorry`s in **small batches (3–5)** using `sledgehammer` / `process_theories`
5. If sledgehammer fails, you can very cautiously experiment with a subproof.
6. Instead of `by blast` etc always use our safe `by (by100 blast)` , `by (by100 fast)` , `by (by100 simp)`, etc
   methods that limit the time to 100 ms, or the restricted apply (rule ...), apply (erule ...), apply (drule ...) ).
7. If you catch yourself writing anything other than `sorry`:
   → **STOP and replace it with `sorry`**

**Interpretation:**
All proofs are developed in two phases:

* Phase 1: structure (`sorry` only)
* Phase 2: replacement (actual tactics)

Final proofs may use automation, but only after the `sorry`-first phase.

---

## Project structure

* **Main theory:** `AlgTop`
* **Imports:** `Complex_Main` + developed topology

Sessions:

* `Top0` (`tst/i/`): Chapters 2–8 (cached)
* `AlgTop` (`tst/`): algebraic topology

### Build commands

Full build:

```bash
cd /project/tst && /project/bin/isabelle build -D .
```

Incremental:

```bash
/project/bin/isabelle build -D . Top0
/project/bin/isabelle build -D . AlgTop
```

---

## Build discipline (non-negotiable)

Build early and often, especially after:

* changing definitions
* changing statements
* adding/editing proofs
* refactoring structure

A build is successful if:

* the session compiles
* no errors occur
* runtime remains reasonable

Using `sorry` is expected, but **the project must always build**.

---

## Proof development workflow (process_theories + sledgehammer)

Use `process_theories` for development (not `build`):

```bash
/project/bin/isabelle process_theories -d . -l AlgTop -O -o quick_and_dirty \
  -M "Try this|No proof" -f AlgTop.thy
```

### Standard workflow

1. Insert many:

   ```isabelle
   sledgehammer [timeout = 10]
   sorry
   ```

   (or `try0`) across a proof

2. Run `process_theories` **once**

3. Collect all `Try this:` suggestions

4. Replace each `sorry` with the **fastest reasonable proof**

5. Run again to verify correctness and timing

6. Use `isabelle build -D .` only for final verification

### Critical rules

* Never run sledgehammer one step at a time in a loop
* Always annotate many steps and run once
* Always verify real runtime (kernel time ≠ reported time)
* If a step is slow: restructure or try alternative suggestions

Remove all `sledgehammer` / `try0` calls after extracting proofs.

---

## Performance and tactic discipline

Automation in `AlgTop` can easily explode.

### High-risk tactics

* `simp`, `simp_all`
* `auto`, `force`, `fastforce`
* `blast`
* `meson`, `metis`, `smt`

### Rules

* Avoid opaque one-shot proofs:

  ```isabelle
  by (auto simp: ...)
  ```

* Prefer explicit steps:

  ```isabelle
  apply (simp add: ...)
  apply (intro ...)
  apply blast
  done
  ```

* Prefer restricted simplification:

  ```isabelle
  apply (simp only: ...)
  apply (simp add: ... del: ...)
  ```

* On complex goals, prefer:

  ```isabelle
  apply (rule ...)
  apply (erule ...)
  apply (drule ...)
  ```

### If something times out

1. Replace the last step with `sorry`
2. Recompile
3. Reintroduce the step in smaller pieces
4. Replace broad automation with explicit reasoning

### Golden rule

If a tactic touches:

* quantifiers
* large disjunctions
* many rewrites from `Complex_Main`
* heavy algebra

→ assume it can explode
→ proceed incrementally and explicitly

---

## Formalization policy

Goal: faithful, gradual formalization of `/project/algtop.tex`.

### Guidelines

* State the **correct theorem first**, even with `sorry`
* Prefer many small helper lemmas over long proofs
* Keep the build green at all times
* Fix bad definitions/statements instead of working around them
* Prioritize major theorems across the whole file
* Avoid exercises/examples unless needed later
* Do not shy away from proving hard theorems that take long time - this is a multi-day project, an initial partial proof is ok
* Use Isabelle libraries and the previous general topology before reproving facts
* Remember to use the strict/defensive versions of predicates introduced to comply with the review
* Follow `algtop.tex` when useful, but restructure if needed

---

## Theory structure and style

* Keep `AlgTop.thy` readable (`section`, `subsection`, `text`)
* Do not introduce a separate “Background” section
* Prefer structured proofs and named helper lemmas
* Control simp sets carefully (avoid global explosions)

Naming:

* definitions: consistent prefix (e.g. `top1_...`)
* lemmas: descriptive, with `_intro`, `_elim`, `_simp`, `_iff` where appropriate

---

## Diagnostics and tooling

### Useful commands

Process file quickly:

```bash
/project/bin/isabelle process_theories -d . -l AlgTop -o quick_and_dirty -f AlgTop.thy
```

Find useful theorems:
```
/project/bin/isabelle eval_at -d . -l Top0 AlgTop.thy 100 'find_theorems "_ + _ = _ + _"'
```

Show proof states:

```bash
/project/bin/isabelle process_theories -O -o show_states -l AlgTop -f AlgTop.thy \
  | grep -A10 '\b\(XXX\|YYY\|ZZZ\)'
```

Timing:

```bash
project/bin/isabelle eval_at -t -d . -l Top0 AlgTop.thy [second-to-last-line] > timing_info_XXX
```

Use timing regularly; aim for total runtime well below ~30s.

### Searchable indexes

Two indexes cover all sessions. **Regenerate after caching or adding theorems.**

```bash
cd /project/tst && bash gen_index.sh       # THEOREMS_AND_DEFS.txt – name/kind/file/line
cd /project/tst && bash gen_stmt_index.sh   # STMT_INDEX.txt – name + statement fragment
```

Before stating a new lemma/definition, **grep both indexes** to avoid duplicates:

```bash
grep -i "keyword" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

---

## Change management

Work in small, validated increments.

* Create numbered backups: `bckXXXX`

* Maintain corresponding `CHANGESXXXX`

* Validate each backup with:

  ```bash
  cd /project/tst && /project/bin/isabelle build -D .
  ```

* Commit frequently with clear descriptions

* At the end of each session, regenerate the theorem index:

  ```bash
  cd /project/tst && bash gen_index.sh
  ```

  Before stating a new lemma/definition, check `THEOREMS_AND_DEFS.txt`
  to avoid duplicating existing results (grep for keywords).

---

## One-line summary

**Always keep `AlgTop` building; write new proofs with `sorry` only, replace them in batches using `process_theories`, and keep proofs explicit, fast, and maintainable.**

