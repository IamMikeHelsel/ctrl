# Architecture

## Machines and roles

| | Mac (M4 Max, 16 cores, 64 GB) | Spark (`sparky.local`: GB10, 20 ARM cores, 121 GB unified, 2.7 TB) |
|---|---|---|
| Role | High level: plan, review, interactive proof | Local solve: search, batch check, autonomous prover |
| Lean | elan; toolchain from `erdos/lean-toolchain` | elan; same toolchain, Linux `bwrap` sandbox available |
| Models | Claude Code (cloud) | Ollama: Leanstral 1.5 (119B-A6B, Q4_K_M) for proving; gpt-oss-120b / qwen for triage |
| Solvers | — | Kissat 4.x, CaDiCaL 3.x (LRAT), OR-Tools CP-SAT, cvxpy + Clarabel/SCS/HiGHS in `~/venvs/solve` |
| Repo copy | `~/Dev/ctrl` (source of truth) | `~/lean-work/ctrl` (rsync'd by `ctrl spark sync`, never edited by hand) |

The Mac is the source of truth. The Spark receives the repo with `rsync`, excluding `.lake/`, and sends
results back in `work/NNN/` (logs, certificates, candidate proofs). Nothing on the Spark is
authoritative until it has been pulled back and has passed `ctrl check` on the Mac.

## The challenge / solution contract

```
erdos/Challenge/Erdos834.lean       -- frozen; human-approved
  namespace Challenge.Erdos834
  /-- statement copied from FormalConjectures.ErdosProblems.«834» (Apache-2.0) -/
  def statement : Prop := …
  -- approved-by: mike 2026-10-17

erdos/ErdosLab/Erdos834.lean        -- the work
  import Challenge.Erdos834
  theorem Challenge.Erdos834.solution : Challenge.Erdos834.statement := …
```

`ctrl check NNN` passes only if all of the following hold:
1. `lake build` succeeds for both modules.
2. The solution file contains no forbidden tokens (docs/erdos-lab/rules.md).
3. `#print axioms Challenge.ErdosNNN.solution` lists only the three standard axioms.
4. The solution's type is *syntactically* `Challenge.ErdosNNN.statement`. It is checked by an
   elaborated Lean script, not by grep.
5. The challenge file carries an `approved-by` line and its hash matches `work/NNN/status.json`, so
   any edit after approval is caught.

This is the same idea as Palomar's comparator (challenge statement separate from proof). Packaging
for Palomar is `ctrl package NNN`, planned.

## Data flow

```
data/erdos/*.csv ──ctrl targets──▶ pick NNN
                                     │ ctrl new NNN
                                     ▼
            erdos/Challenge/ErdosNNN.lean (draft) ── human review ──▶ ctrl approve NNN --by mike
                                     │
              ┌──────────────────────┼─────────────────────────┐
              ▼                      ▼                         ▼
    Mac: Claude Code         Spark: ctrl spark prove     Spark: ctrl spark solve
    (planner/prover          (Leanstral + lean-lsp-mcp,  (SAT/CP-SAT/SDP → certificate
     subagents)               budgeted, in a scratch      in work/NNN/certs/)
                              copy, returns a diff)
              └──────────────────────┼─────────────────────────┘
                                     ▼
                ctrl check NNN (Mac) + ctrl spark check NNN (Linux)
                                     ▼
                improve: golf, docstrings, exposition, disclosure ──▶ commit / PR
```

## What runs where, and why
- **Interactive proving on the Mac.** Latency and judgement matter most there, and Claude is the
  strongest prover available for research-style analysis.
- **Autonomous proving on the Spark.** Leanstral is free to run, so it can grind on many small goals
  in parallel worktrees overnight. Its output is untrusted until `ctrl check` passes.
- **Search on the Spark.** It has 20 cores, lots of RAM, and the solvers. Every search must produce
  a certificate that Lean re-checks.
- **Final checks on both machines.** Linux is where Lean's sandboxed checkers (`lake check`,
  comparator, v4.35+) run. A clean build on a second machine catches environment leaks.
