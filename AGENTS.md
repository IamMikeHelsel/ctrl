# Working on ctrl

ctrl produces machine-checked Lean proofs and the evidence that they prove the right statement.
**Faithfulness is the product.** A proof of a slightly different statement is worth nothing.

## Hard rules
- **Never edit a file under `lean/Challenge/` after it is approved.** The approval marker is the
  `-- approved-by:` line. Challenge files hold the frozen statement as a `def … : Prop`. Changing one
  requires a human, with `ctrl approve NNN --by <name>` after review.
- Solutions prove `theorem solution : Challenge.ErdosNNN.statement` (the `Prop` itself, not a
  restatement). `ctrl check` enforces this.
- In `lean/ErdosLab/`, never use `sorry`, `admit`, `axiom`, `opaque`, `implemented_by`, `native_decide`,
  `set_option maxHeartbeats` above 400000, or `set_option debug.*`. `#print axioms solution` must show
  only `propext`, `Classical.choice`, `Quot.sound`.
- Prover agents may not add new `def`s that appear in the statement's dependencies. They may add
  lemmas and private helpers.
- Big search results (SAT, CP-SAT, SDP) count only as **certificates Lean re-checks**: an explicit
  witness checked by `decide`, a rational SDP certificate checked by `norm_num`, or an LRAT proof.
  A solver's "UNSAT" on its own proves nothing. `bv_decide`/`lrat_proof` add the axiom
  `Lean.ofReduceBool`. That is allowed only when `work/NNN/status.json` sets
  `"axiom_tier": "reduceBool"`, and it must be disclosed (docs/decisions.md D3).
- Disclose AI use honestly in `work/NNN/disclosure.md`. Never present AI-written expositions as
  hand-written. erdosproblems.com and the Justin Sun Prize both require this.
- Don't copy erdosproblems.com text into the repo. Link to it. Formal Conjectures statements are
  Apache-2.0 and fine to reuse with attribution.

## Conventions
- Python: `uv` only (`uv sync`, `uv run`). Python ≥ 3.11, typer CLI, ruff line length 100.
- Lean: `elan` + `lake`. The toolchain is pinned in `lean/lean-toolchain` to match Formal Conjectures.
  Compile one file with `lake env lean <file>`, and run full `lake build` only at checkpoints.
- The CLI is an API (docs/cli.md). Every command ends with `ui.finish(data, next=[...])`, and failures
  raise `CtrlError(code, message, hint, fix, exit_code)`. Keep JSON envelopes, error codes and exit
  codes stable. `tests/test_cli.py` pins them.
- Per-problem state lives in files under `work/NNN/` (`plan.md`, `log.md`, `certs/`, `status.json`
  written by the CLI). `ctrl status` derives next steps from files. Don't add hidden state.
- Remote work goes through `ctrl spark …`, which runs the scripts in `tools/spark/` over SSH.
  Don't hand-roll ssh in other places.
- Order tests by how likely they are to catch a real bug: statement binding and audit first, then
  CLI contract, then plumbing. Keep the Python suite under ~5 s, and don't call Lean or SSH in unit
  tests. Mark those `@pytest.mark.integration`.

## Before handing off
```sh
uv run ruff check . && uv run ruff format --check . && uv run pytest -q
uv run ctrl check --all        # every solution builds, audits clean, binds to its challenge
```
Record new default decisions in docs/decisions.md.
