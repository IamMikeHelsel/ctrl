# Instructions for agents working on `ctrl`

`ctrl` is a Lean 4 + Mathlib library of machine-checked results in controls, systems,
estimation, applied math and machine vision. Read `README.md` for design and `ROADMAP.md`
for what to work on next.

## Hard rules

1. **No escape hatches.** No `sorry`, `admit`, `axiom`, `native_decide`, or `implemented_by`
   in `ControlsLean/`. `scripts/check.sh` enforces this and CI runs it.
2. **Standard axioms only.** Every headline theorem is listed in `scripts/Audit.lean` and
   must depend only on `propext`, `Classical.choice`, `Quot.sound`.
3. **Never weaken a statement to make it compile.** If a theorem is false as stated, fix the
   statement and say so in the commit message. Don't silently add hypotheses.
4. **Docstrings must match what is proved.** Don't claim properties in a module doc that
   have no theorem behind them.
5. **Don't commit `.lake/`.** The Mathlib cache is ~5 GB.

## Setup (once per machine)

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
source ~/.elan/env
lake exe cache get      # downloads prebuilt Mathlib, ~2 min
```

## The loop (one target at a time)

1. Pick the top unclaimed item in `ROADMAP.md`. Create a branch `target/<short-name>`.
2. Write the statement first, in a new file under the right area folder
   (`Controls/`, `Estimation/`, `Vision/`, `AppliedMath/`), with the proof as `by sorry`.
   Make sure the *statement* typechecks and reads like the textbook result.
3. Iterate on the proof with `scripts/check.sh ControlsLean/Area/File.lean` (~5 s per run).
   Prefer small private lemmas over one huge proof. Search Mathlib before proving
   something general: `rg -n "theorem .*keyword" .lake/packages/mathlib/Mathlib`.
4. Add the file to `ControlsLean.lean` and its headline theorems to `scripts/Audit.lean`.
5. Run `scripts/check.sh` (full build, escape-hatch ban, axiom audit). It must print `OK`.
6. Update the results table in `README.md` and move the item to *Done* in `ROADMAP.md`.
7. Commit, push, open a PR. CI must be green before merge.

## Erdős lab (`erdos/`, `work/`, `src/ctrl/`, `tools/spark/`)

Bounty formalizations of Erdős problems live in the separate Lake project `erdos/`, pinned to
Formal Conjectures' toolchain, not in `ControlsLean/`. Its rules are in
[docs/erdos-lab/rules.md](docs/erdos-lab/rules.md). The key ones:
- Never edit an approved `erdos/Challenge/ErdosNNN.lean`.
- Solutions prove `Challenge.ErdosNNN.statement` itself.
- Gate with `uv run erdos check NNN`.
- Spark output stays untrusted until `erdos promote`.

Its dev → test → improve loop and subagents are described in
[docs/erdos-lab/loop.md](docs/erdos-lab/loop.md).

## Style

* File header: copyright block, imports, then a `/-! # Title ... -/` module docstring
  stating the result in math terms and listing what is proved.
* Namespace `ControlsLean.<Area>`. Lines ≤ 100 chars. Mathlib naming conventions
  (`snake_case` theorems, `UpperCamelCase` defs/structures).
* State results in the most general setting that costs nothing extra (any field instead of
  `ℝ`, linear maps instead of matrices), then add a concrete corollary engineers recognise
  (mass–spring–damper, PD control, etc.).

## Gotchas seen so far

* `A ^ i ∘ₗ B` parses as `A ^ (i ∘ₗ B)`; write `(A ^ i) ∘ₗ B`.
* `LinearMap.range` needs `open LinearMap (range)` to be written `range`.
* `Matrix.PosDef` is stated with `Finsupp`; use `posDef_iff_dotProduct_mulVec` to get the
  `star x ⬝ᵥ (M *ᵥ x)` form.
* `push_neg` is deprecated in this Mathlib; use `push Not`.
* Compactness of the unit sphere (`isCompact_sphere`) is the standard way to get
  `c‖x‖² ≤ xᵀMx` from positive definiteness; see `DiscreteLyapunov.exists_quad_lower`.
