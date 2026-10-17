# Decisions

- **D1. Pin Formal Conjectures, don't fork it.** The `lean/` project requires FC at commit
  `d9ce556` (Lean/Mathlib v4.33.1). Challenge statements are copied *verbatim* from FC with
  attribution, so the wording is the community-reviewed one. Bump the pin deliberately with
  `lake update` and re-run `ctrl check --all`.
- **D2. Bind solutions to a `Prop`, not to a restated theorem.** `def statement : Prop` in Challenge
  and `theorem solution : statement` in ErdosLab. That makes the solution's statement correct by
  construction, and `ctrl check` only has to confirm the type and the hash.
- **D3. Two axiom tiers.** The default tier allows only `propext`, `Classical.choice` and `Quot.sound`.
  The `reduceBool` tier also allows `Lean.ofReduceBool`, which `bv_decide`/`lrat_proof` need for
  large SAT certificates. It is opt-in per problem in status.json and disclosed in disclosure.md.
  Prefer kernel `decide` when the instance is small enough. `native_decide` is never allowed.
- **D4. The Mac is the source of truth.** The Spark holds an rsync'd copy and returns candidates.
  Nothing moves into `lean/` without a Mac-side check.
- **D5. uv for all Python**, including the solver venv on the Spark (`~/venvs/solve`, created with
  `uv venv`). There is no conda and no system pip.
- **D6. Local prover = Leanstral 1.5 (119B-A6B, Q4_K_M GGUF) in the Spark's Ollama.** It is driven
  by headless Claude Code pointed at Ollama's Anthropic-compatible endpoint, with lean-lsp-mcp. It's
  free, so it gets volume work. Claude on the Mac gets judgement work.
- **D7. Lean toolchain lag.** FC is on v4.33.1. `lake check`/`lake comparator` arrive in v4.35, so
  until FC bumps, binding is checked by our own elaborated script (architecture.md, check 4).
