# The dev → test → improve loop

One problem moves through the loop at a time. Several problems can be in flight in separate git
worktrees. Each stage has an owner (a Claude Code subagent in `.claude/agents/`, or a human), a
command that ends it, and an artifact on disk.

```
 select ─▶ state ─▶ [human approve] ─▶ dev (prove / solve) ─▶ test (check) ─┬─▶ improve ─▶ ship
                                             ▲                              │
                                             └──── failure report ──────────┘
```

| Stage | Owner | Ends with | Artifact |
|---|---|---|---|
| select | `target-scout` | a chosen NNN and a 5-line rationale | `work/NNN/plan.md` (Why section) |
| state | `statement-drafter` | `ctrl new NNN`, then a review note comparing the FC statement with the source paper | `lean/Challenge/ErdosNNN.lean` (draft), plan.md (Statement review) |
| approve | **human** | `ctrl approve NNN --by NAME` | approved-by line + hash |
| plan | `proof-planner` | a blueprint: a lemma DAG with each node stated in Lean (as `sorry`), each tagged *mathlib*, *elementary*, *search* or *hard* | plan.md (Blueprint), skeleton in ErdosLab/ErdosNNN.lean |
| dev: prove | `lean-prover` (Mac) or `ctrl spark prove` (Leanstral) | lemmas filled, with `ctrl check NNN --fast` green per lemma | ErdosLab/ErdosNNN.lean, candidates/ |
| dev: solve | `solver-engineer` | `ctrl spark solve NNN search.py` produces a certificate, plus a Lean file that re-checks it | work/NNN/certs/, ErdosLab/ErdosNNN/Cert.lean |
| test | `lean-verifier` | `ctrl check NNN` and `ctrl spark check NNN` both green, plus an adversarial review: is the statement vacuous, is the binding right, did any def drift? | status.json (checked) + log.md (Verifier report) |
| improve | `lean-improver` | golfed proof, docstrings, a human-readable exposition draft, `disclosure.md`. Does not change statements. | ErdosLab/*, work/NNN/exposition.md |
| ship | human | commit/PR; later `ctrl package NNN` for Palomar or JSP | — |

## Rules that keep the loop honest
- **Failures route back with evidence.** The verifier writes a short failure report in log.md: the
  failing check, the exact error, and a suggested next move. The prover starts from that report, not
  from scratch.
- **Budgets.**
  - Mac prover: 3 distinct approaches per lemma, then split the lemma or escalate it to the planner.
  - Spark prover: `--minutes` and `--attempts`, and it always returns a diff even when it fails.
- **Untrusted until checked.** Anything produced on the Spark arrives in `work/NNN/candidates/`, and
  a Mac agent promotes it into `lean/` only after `ctrl check --fast` passes.
- **No statement edits after approval** by any agent. If the statement looks wrong, the verifier
  stops the loop with exit 3 and asks the human.
- **Search results are certificates.** See AGENTS.md: Lean re-checks them, or they don't count.

## Running it
From a Claude Code session in this repo, either:
- ask for a stage ("run the loop on 1216", "verify 834"); the main session delegates to the matching
  subagent and reports back after each stage, or
- run stages yourself through the CLI. Every `ctrl` command prints the next one.
