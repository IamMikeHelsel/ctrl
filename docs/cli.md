# `ctrl` CLI contract

`ctrl` is a uv-managed Python package (typer). Treat it as an API: agents call it, and the
envelope, error codes and exit codes are pinned by `tests/test_cli.py`.

## Output
- **rich**: a human at a terminal.
- **plain**: pipes, CI, and agents. It is chosen automatically when `CLAUDECODE` or `CTRL_AGENT` is
  set, or stdout is not a TTY.
- **json**: `--json` or `CTRL_JSON=1`. Exactly one envelope on stdout:
  `{"ok": bool, "command": str, "data": {...}, "warnings": [str], "next": [str], "error": null | {"code","message","hint","fix"}}`.
  Progress goes to stderr.

Every command ends with `next`: the exact commands that move things forward.

## Exit codes
| Code | Meaning |
|---|---|
| 0 | ok |
| 1 | error (bad environment, missing tool, IO) |
| 2 | usage |
| 3 | needs a human (statement not approved, review pending). Wait; don't retry. |
| 4 | a check failed (build, forbidden token, axiom, statement binding, hash drift) |
| 5 | remote unavailable (Spark unreachable, job not found) |

## Commands (v0.1)

| Command | What it does | Key data fields |
|---|---|---|
| `ctrl doctor [--remote/--no-remote]` | Checks elan/lake/toolchain, uv and the Lean cache locally. With remote, also checks the same plus kissat, cadical, `~/venvs/solve`, ollama + the leanstral model and lean-lsp-mcp on the Spark | `checks: [{name, where, ok, detail}]` |
| `ctrl targets [--tab open\|formalize] [--top N] [--prize] [--max-difficulty D] [--min-fit F]` | Ranked rows from `data/erdos/*.csv` | `rows` |
| `ctrl new NNN [--force]` | Writes `lean/Challenge/ErdosNNN.lean` (statement `def` copied from the pinned Formal Conjectures file, with attribution), the solution skeleton `lean/ErdosLab/ErdosNNN.lean` with `sorry`, `work/NNN/{plan.md,log.md,status.json}`, and registers both modules. If FC has several theorems for NNN, `--part NAME` picks one. | `files`, `fc_theorems` |
| `ctrl approve NNN --by NAME` | Records `-- approved-by:` and the challenge hash in status.json. Refuses without `--by`. | `hash` |
| `ctrl check [NNN \| --all] [--fast]` | Runs the five checks in architecture.md and writes the result to status.json. `--fast` uses `lake env lean` on the solution only. | `results: [{nnn, build, tokens, axioms, binding, hash}]` |
| `ctrl status` | One row per `work/NNN`: phase (draft, approved, proving, checked, packaged) and next step | `problems` |
| `ctrl spark sync` | rsync the repo to `~/lean-work/ctrl` (excludes `.lake/`, `.git/`), then `lake exe cache get` if the manifest changed | `changed` |
| `ctrl spark check NNN` | `sync`, then `tools/spark/check.sh NNN` remotely | as `check` |
| `ctrl spark prove NNN [--minutes M] [--model leanstral] [--attempts K]` | `sync`, then `tools/spark/prove.sh` in tmux: a scratch copy, a headless agent on the local model with lean-lsp-mcp, a budget. Returns a job id. | `job` |
| `ctrl spark solve NNN SCRIPT [-- args]` | Runs `work/NNN/SCRIPT` in `~/venvs/solve` with the solvers on PATH, in tmux. Returns a job id. | `job` |
| `ctrl spark jobs` / `ctrl spark log JOB [-f]` / `ctrl spark fetch JOB` | List jobs, tail a log, or pull results into `work/NNN/` (candidates land in `work/NNN/candidates/JOB/`, never directly in `lean/`) | |

## Error codes (stable)
`TOOL_MISSING`, `LEAN_BUILD_FAILED`, `FORBIDDEN_TOKEN`, `NONSTANDARD_AXIOM`, `BINDING_MISMATCH`,
`CHALLENGE_DRIFT`, `NOT_APPROVED`, `NO_FC_STATEMENT`, `NEEDS_ANSWER`, `EXISTS`, `SPARK_UNREACHABLE`,
`JOB_NOT_FOUND`, `REMOTE_FAILED`, `BAD_USAGE`, `INTERNAL`.

- `NEEDS_ANSWER` (exit 3): the FC statement leaves the answer open (`answer(sorry)`, or a
  `def …answer := sorry` it refers to). A challenge must state the actual answer, so a human fills it in.
  `ctrl approve` also refuses a challenge that still contains `sorry`.
- `REMOTE_FAILED` (exit 1): the Spark was reachable but a remote step failed (`lake exe cache get`,
  a `tools/spark/*.sh` that printed no job id, an unreadable `meta.json`).
- `INTERNAL` (exit 1): a bug in ctrl.
