# Machines

As set up on 2026-10-17. `ctrl doctor` verifies all of this.

## Mac: MacBook Pro M4 Max, 64 GB
- `elan` in `~/.elan` (on PATH via `~/.zprofile`; non-login shells need `source ~/.elan/env`). The
  default toolchain is `stable` (4.35.0). `lean/` pins 4.33.1 through `lean-toolchain`.
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
| Ollama model `leanstral` | Ollama 0.34.2 | `ollama create leanstral -f tools/spark/Modelfile.leanstral` |

The Mathlib cache (`lake exe cache get`) works on linux-aarch64. A cold build of the FC dependency
takes about 100 s.

Other Ollama models already on the Spark: `spark-fast` (Qwen3.6 35B MoE), `spark-general`,
`spark-deep` (gpt-oss 120B), `spark-vision`. `spark-code` (Qwen3-Coder-Next) crashes CUDA, so avoid it.
`~/Dev/spark-tools/spark-ai` on the Mac tunnels Ollama to `127.0.0.1:11435`.
