# Machines

As set up on 2026-10-17. `ctrl doctor` verifies all of this.

## Mac: MacBook Pro M4 Max, 64 GB
- `elan` in `~/.elan` (on PATH via `~/.zprofile`; non-login shells need `source ~/.elan/env`). The
  default toolchain is `stable` (4.35.0). `erdos/` pins 4.33.1 through `lean-toolchain`.
- `uv` (Homebrew).
- `~/Dev/formal-conjectures`: a reference clone at the same pin, handy for browsing statements.
- Claude Code, run from the repo root. Recommended MCP: `claude mcp add lean-lsp -s project uvx lean-lsp-mcp`.

## Spark: `sparky.local` (DGX Spark, GB10, 20 cores aarch64, 121 GB unified, Ubuntu 24.04)
SSH works through NVIDIA Sync's key. The alias is `sparky.local`; `SPARK_SSH_HOST` overrides it.
There is no sudo, so everything is user-level.

| Thing | Where | Rebuild |
|---|---|---|
| elan + Lean | `~/.elan` | `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \| sh -s -- -y` |
| uv | `~/.local/bin/uv` | `curl -LsSf https://astral.sh/uv/install.sh \| sh` |
| Kissat 4.0.4, CaDiCaL 3.0.1 | `~/opt/bin` | `git clone` arminbiere/{kissat,cadical}, then `./configure && make` |
| Solver venv | `~/venvs/solve` | `uv venv ~/venvs/solve && uv pip install python-sat ortools networkx numpy scipy sympy cvxpy clarabel scs` |
| Claude Code 2.1.x | `~/.local/bin/claude` | `curl -fsSL https://claude.ai/install.sh \| bash` |
| lean-lsp-mcp | `~/.local/bin/lean-lsp-mcp` | `uv tool install lean-lsp-mcp` |
| Repo copy | `~/lean-work/ctrl` | `ctrl spark sync` |
| Leanstral GGUF | `~/models/leanstral/` | `uvx --from 'huggingface_hub[hf_xet]' hf download GZGavinZhao/Leanstral-1.5-119B-A6B-GGUF Leanstral-1.5-119B-A6B-Q4_K_M.gguf --local-dir ~/models/leanstral`. Ollama's own `hf.co/` pull fails on the xet CDN redirect. |
| Ollama model `leanstral` | Ollama 0.34.2 | `bash tools/spark/build-leanstral.sh` (patches the chat template, then `ollama create`; see Spark prover) |

The Mathlib cache (`lake exe cache get`) works on linux-aarch64. A cold build of the FC dependency
takes about 100 s.

Other Ollama models already on the Spark: `spark-fast` (Qwen3.6 35B MoE), `spark-general`,
`spark-deep` (gpt-oss 120B), `spark-vision`. `spark-code` (Qwen3-Coder-Next) crashes CUDA, so avoid it.
`~/Dev/spark-tools/spark-ai` on the Mac tunnels Ollama to `127.0.0.1:11435`.

## Spark prover (tools/spark)
`ctrl spark …` runs these over SSH; each also works by hand on the Spark (`bash ~/lean-work/ctrl/tools/spark/X.sh`).
Non-login SSH shells lack `~/.local/bin` and elan, so every script sources `tools/spark/env.sh` first.

| Script | What it does |
|---|---|
| `check.sh NNN [--fast]` | `erdos/scripts/check.sh` in `~/lean-work/ctrl`, stdout and exit code passed through |
| `prove.sh NNN [--minutes M] [--model leanstral] [--attempts K]` | job dir + scratch copy, starts `prove-run.sh` in tmux `ctrl-JOB`, prints `{"job": ID}` |
| `solve.sh NNN SCRIPT [args…]` | `~/venvs/solve/bin/python work/NNN/SCRIPT args` in tmux, cwd `outputs/`, `~/opt/bin` on PATH. Optional `SOLVE_TIMEOUT_MIN` |
| `jobs.sh` / `log.sh JOB [-f] [-n N]` | all `meta.json` as a JSON array (newest first; `running` with no tmux session shows as `lost`) / tail the log; `-f` stops when the job ends; exit 5 if the job is missing |
| `build-leanstral.sh` | (re)builds the `leanstral` Ollama model, see below |

**Jobs** live in `~/lean-work/jobs/<YYYYMMDD-HHMMSS>-<NNN>-<kind>-<hex4>/`: `log.txt`, `meta.json`
(`job, nnn, kind, started, status, model, budget, tmux`, then `finished, elapsed_s`, plus
`attempts_done` for prove and `exit_code` for solve), and `outputs/`. The status is one of
`running`, `success`, `failed`, `timeout` or `cancelled`. To cancel a job, run
`tmux kill-session -t ctrl-JOB`. Delete old jobs by hand.

**prove** copies `erdos/` and `work/NNN/` into `JOB/scratch/` (with `.lake/packages` symlinked to the
repo copy's and `.lake/build` copied after `lake build Challenge.ErdosNNN`), makes `Challenge/`
read-only, and runs up to K headless `claude -p` attempts (prompt: `tools/spark/prove_prompt.md`).
The remaining wall clock is split evenly over the remaining attempts. Each attempt gets the
previous attempt's check output and keeps its edits. Claude Code points at Ollama (`ollama_claude_env`
in env.sh) with lean-lsp-mcp (`lean_build` disabled, because it could run `lake clean` or
`cache get` on the shared packages) and `--permission-mode acceptEdits`. Allowed tools are
Read/Edit/Write/Glob/Grep, `Bash(lake env lean:*)`, `Bash(lake build:*)` and `mcp__lean-lsp__*`.
Skill, Task and web tools are denied, and each session is capped at `--max-turns 150`.
Sessions use a private `CLAUDE_CONFIG_DIR` (`~/.config/ctrl-prove-claude`), so the Spark user's
skills, plugins and CLAUDE.md never load. Those cost about 7k prompt tokens, and Leanstral looped
on the Skill tool. Optional env for prove.sh: `PROVE_REASONING=high|none`, `PROVE_MAX_TURNS`.
After each attempt the job runs `check.sh NNN --fast` in the scratch, rejects any change under
`Challenge/`, and writes `outputs/attempt-K/{ErdosNNN.lean, diff.patch, check.json, check.exit,
transcript.jsonl, claude.json, prompt.md}`. At the end it writes `outputs/final.lean` and
`outputs/final.patch` (always, even on failure). `ctrl spark fetch` copies `outputs/` to
`work/NNN/candidates/JOB/`.

**Leanstral in Ollama.** The GGUF (arch `mistral4`) works in Ollama 0.34.2, whose llama-server backend
renders the GGUF's *embedded* jinja template and parses Mistral `[TOOL_CALLS]name[ARGS]{…}` calls.
That gives tool calls on both `/api/chat` and the Anthropic shim `/v1/messages`. Thinking comes
back as `thinking` blocks. A Modelfile `TEMPLATE` is parsed as a Go template, and the stock
template rejects what Claude Code sends (several system messages, a user turn right after tool
results). So `build-leanstral.sh` writes `tools/spark/leanstral.jinja` into a copy of the GGUF
(`*.ctrl.gguf`, +72 GB) and runs `ollama create`. Settings: `num_ctx 65536` (73 GB resident,
100% GPU), temperature 1.0, reasoning `high` by default. A per-run override needs no second model:
the template obeys a `[ctrl:reasoning=none|high]` marker in the system prompt, and prove jobs pass
`PROVE_REASONING` (default `high`) that way. Later system messages are rendered in place, not
hoisted, so llama.cpp's KV prefix cache hits (about 22k of 23k prompt tokens reused per turn).
Measured on the GB10: about 45 tok/s decode, 1300 to 1700 tok/s prefill, about 13 s cold load,
and 5 to 20 s per agent turn with Claude Code's ~15 to 25k-token prompt.

Results on a toy goal (`∑ i ∈ range n, (2i+1) = n^2`, 2026-10-17): Leanstral with reasoning `high`
solved it in 200 s (21 turns, one attempt). A repeat needed both attempts (about 11 min).
`spark-fast` solved it in 65 s (10 turns). Reasoning `none` looped (141 identical Reads) and once
restated the statement in `solution`'s type; the check rejects that.

Known quirks: (1) Leanstral sometimes emits a tool call inside an unclosed `[THINK]`, which comes back
as thinking. Claude Code then ends the session, so prove-run resumes it (`--resume`, up to 8
times per attempt). (2) Ollama runs one slot, so concurrent prove jobs or other requests to the model
evict each other's prefix cache. Run one prove job at a time. (3) lean-lsp-mcp's `lean_loogle`
and `lean_leansearch` are remote and rate-limited (about 3 per 30 s), so the prompt steers the model to
`lean_local_search`.
