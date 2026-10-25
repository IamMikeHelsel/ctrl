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

## CLI decisions (v0.1)
- **D8. `ctrl new` copies statements with a scanner, not a Lean parser.** It strips comments, finds
  the depth-0 `:=` that ends the signature, turns binders into `∀ binders, type`, and keeps the text
  verbatim apart from indentation. The `open` lines in scope (and `open ErdosNNN`) are emitted *before*
  `namespace Challenge.ErdosNNN`, because inside it `open ErdosNNN` resolves to the challenge namespace.
  `open X in` right above the FC theorem is kept on the `def`. `variable`s and `local notation` in the
  FC file become review warnings. The shape is pinned byte-for-byte against the build-verified
  `lean/Challenge/Erdos834.lean` (tests/fixtures/golden).
- **D9. Which FC theorem.** Candidates are the theorems named `erdos_NNN…` (helper/test theorems are
  ignored unless there are no others). With more than one, `ctrl new` exits 2 (`BAD_USAGE`) listing
  them in `data.fc_theorems`; `--part` takes the full name or a unique suffix (`parts.ii`, `eighteen`).
  It never guesses, even when a plain `erdos_NNN` exists.
- **D10. Unknown answers.** The pinned FC no longer writes `answer(sorry)`; it writes
  `def erdos_NNN.answer : T := sorry` and uses it in the statement. Both forms (and a bare `sorry` in
  the statement) give `NEEDS_ANSWER`, exit 3.
- **D11. Approval.** `--by` missing → `NOT_APPROVED`, exit 3 (approval is a human act, not a usage
  slip). The hash is taken after the `-- approved-by:` line is written. Re-approving an unchanged
  approved challenge is a no-op; approving after drift re-records line and hash and clears old check
  results. `ctrl new --force` refuses an approved challenge (`EXISTS`, exit 3); for drafts it rewrites
  the challenge, the solution skeleton and status.json but keeps an existing plan.md/log.md.
- **D12. Check aggregation.** A failed check 1–4 or hash drift → exit 4 with the first failing code in
  CHECKS order (build, tokens, axioms, binding, hash); only-unapproved → exit 3 `NOT_APPROVED`. A field
  missing from check.sh's report counts as failed. Output that isn't JSON counts as a failed build.
  check.sh exit 1 → `TOOL_MISSING`, exit 2 → `BAD_USAGE`. The result goes to status.json `last_check`
  (with the solution's sha256, so `ctrl status` can tell when a pass is stale). Phase: a full pass on an
  approved challenge → `checked`, anything else (including `--fast`) → `proving`; `draft` is never
  moved. `ctrl spark check` records `last_spark_check` and does not move the phase.
- **D13. Spark plumbing.** Scripts go to the Spark as `ssh … bash -s` on stdin, so the remote login
  shell (zsh) doesn't matter. rsync targets `lean-work/ctrl/` relative to the remote home and creates it
  with `--rsync-path`. `lake exe cache get` runs when `lean/lake-manifest.json` is in rsync's itemized
  changes *or* the remote has no `.lake/packages/mathlib` yet. ssh exit 255 or any rsync failure →
  `SPARK_UNREACHABLE`, exit 5.
- **D14. Jobs.** `spark prove` refuses an unapproved (exit 3) or drifted (exit 4) challenge before
  anything is sent; `spark solve` does not, since searches can be exploratory. Only `--model` (default
  `leanstral`) is always passed; `--minutes`/`--attempts` are passed only when given, so the script's
  defaults apply. Job ids are appended to status.json `jobs`. `spark fetch JOB` rsyncs `outputs/` into
  `work/NNN/candidates/JOB/` (a directory, since a job produces several files; the proof candidate
  is `final.lean`), with NNN from the job's `meta.json`. `spark log -f` streams raw text, so it refuses
  `--json`.
- **D15. Defaults.** `ctrl doctor` checks the Spark by default (`--no-remote` skips it), as the README's
  quick start implies. `ctrl targets` defaults to `--tab open`; `--max-difficulty` filters on
  `difficulty_1to5` (open) or `formalization_effort_1to5` (formalize); `--min-fit` on `ai_lean_fit_1to5`
  (open) or `priority_1to5` (formalize). The envelope has exactly the six documented keys (no
  `exit_code`); `next` is a list of command strings.
- **D16. Sync guard.** Before rsync, one ssh call reads `tools/spark/jobs.sh` and the remote
  manifest's sha256. If a prove job is `running`/`starting` and the remote manifest differs from the
  local one, sync refuses with `JOB_RUNNING`, exit 3 (`--force` on `ctrl spark sync` overrides). Syncs
  that don't touch the manifest are allowed under a running job: prove works in its own scratch copy.
- **D17. Promotion.** `ctrl promote NNN JOB` needs an approved, undrifted challenge, the job's
  `final.lean`, and at least one `attempt-*/challenge.diff`, all empty (no diff file means "can't
  tell", which is refused as `CHALLENGE_DRIFT`). It copies `final.lean` over the solution, runs the
  `--fast` check and restores the previous file on any failure, including a crash. Only `final.lean`
  is promoted; a `final-subdir/` is left for a human.
- **D18. Remote knobs.** `--reasoning`/`--max-turns` (prove) and `--timeout-min` (solve) become
  `PROVE_REASONING`, `PROVE_MAX_TURNS` and `SOLVE_TIMEOUT_MIN` env prefixes on the remote command,
  and are passed only when given.
- **D19. Exploratory control lemmas are not approved plant results.** `lean/Research/` contains
  mathematical research lemmas and is included in the default checkpoint build. It uses the
  default axiom tier and prints axiom dependencies. `ctrl check --all` remains the existing
  challenge-bound Erdős check; compiling Research does not create or approve a physical model.
  Control guarantees must state the dynamics, admissible inputs, disturbances, and trajectory
  regularity explicitly. Finite sample checks alone are not continuous-time safety evidence.
- **D20. Timed crossover research is evidence-led and file-backed.** The authorized 60-question
  campaign lives under `work/pod/crossover-60-20261018/`. Its frozen roster separates source
  inventory from completed research, and each initial review requires ten substantive elapsed
  minutes plus independent critique. GO authorizes a bounded next experiment, not a discovery
  claim. Finish breadth coverage before extensions; record actual model access, interruptions,
  resource limits and evidence tiers. Existing challenges and other active pods remain separate.
- **D21. Local factory proof slices remain separately evidenced.** `tools/factory/` reuses a
  hash-recorded copy of the existing 44 controller in a fresh sealed Spark workspace. Only proof
  bodies are generated; exact statements, kernel checks and standard-axiom audits are protected.
  All preflight compilations use the same resource limits as acceptance. Local model attempts,
  infrastructure failures, independent replays and Codex repairs must be attributed separately.
  The 60-idea inventory does not complete timed campaign reviews. These exploratory helper
  contracts neither edit nor approve `lean/Challenge/` files. Use the existing Spark transport
  and cooperative host lock; no whole-repo sync, cloud inference fallback or daemon is introduced.
- **D22. Public research claims are scoped to replayable evidence.** The October 2026
  robotics survey stores source dates, inspected passages, assumptions, proposed transfers,
  baselines and falsifiers under `docs/research/2026-10/`. Exact experiments and disclosure
  live under `work/research/2026-10/`; this is exploratory state, not approved Challenge state.
  Research modules are compiled and axiom-audited separately from `ctrl check --all`.
  Python declaration-name links do not establish semantic refinement; simulation, exact
  arithmetic, formal algebra, runtime equivalence and hardware results remain separate claims.
  The site exports only curated artifacts and hashes. Its legacy idea JSON is explicitly
  deprecated in favor of `research.json`; the historical docs catalog is preserved for review.
  No research default changes repository visibility or deploys the dirty working tree.
