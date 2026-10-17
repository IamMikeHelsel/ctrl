# ctrl

**Lean solves.** A small lab for producing machine-checked proofs of open and solved problems, mostly
Erdős problems and control theory. It splits work between a laptop and a DGX Spark:

- **Mac**: the **high level**. Pick targets, review statements, plan proofs, do hard interactive Lean
  work with Claude Code and `lean-lsp-mcp`, write expositions.
- **Spark** (`sparky.local`): **local solve**. Long-running jobs:
  - SAT and CP-SAT searches (Kissat, CaDiCaL, OR-Tools);
  - SDP and flag-algebra numerics (cvxpy);
  - Lean batch builds and kernel checks (Linux `bwrap` sandbox);
  - a local Lean prover model (Leanstral 1.5 via Ollama) that runs sorry-filling loops on its own.

Every result is checked the same way: a frozen **challenge** statement, a **solution** that is
proved against that exact `Prop`, an axiom audit, and a build on both machines. See
[docs/architecture.md](docs/architecture.md).

## Quick start

```sh
uv sync                        # Python CLI + dev tools (ruff, pytest)
uv run ctrl doctor             # check toolchains on this Mac and on the Spark
uv run ctrl targets --top 15   # best-ranked Erdős targets from data/erdos/
uv run ctrl new 1216           # scaffold challenge + solution + work/1216/plan.md
uv run ctrl check 1216         # build, audit, check the statement binding (local)
uv run ctrl spark check 1216   # same on the Spark (clean Linux build + kernel replay)
uv run ctrl status             # where every problem stands and what to run next
```

The Lean project lives in [`lean/`](lean/). It depends on DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) at a pinned commit, so the
statement wording is the community one.

## Docs

| Doc | What it covers |
|---|---|
| [docs/architecture.md](docs/architecture.md) | Machines, roles, data flow, the challenge/solution contract |
| [docs/loop.md](docs/loop.md) | The dev → test → improve loop and the subagents that run it |
| [docs/cli.md](docs/cli.md) | `ctrl` commands, JSON envelope, exit codes (an API, kept stable) |
| [docs/targets.md](docs/targets.md) | Where targets come from, and the prize and submission rules |
| [docs/machines.md](docs/machines.md) | Exact setup of the Mac and the Spark, and how to rebuild it |
| [docs/decisions.md](docs/decisions.md) | Default decisions and why |
| [AGENTS.md](AGENTS.md) | Rules for any agent (or human) working in this repo |
