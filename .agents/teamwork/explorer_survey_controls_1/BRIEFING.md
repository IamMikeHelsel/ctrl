# BRIEFING — 2026-10-19T05:17:00Z

## Mission
Deeply analyze Mike's three candidate control certificate seeds on the 12-state centroidal SE(3) floating-base template against 2024-2026 literature, evaluate computational feasibility, define verification pathways and falsification tests, and rank by tractability and impact.

## 🔒 My Identity
- Archetype: explorer
- Roles: explorer, analyst, synthesist
- Working directory: /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_controls_1
- Original parent: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Milestone: Candidate seed deep analysis on 12-state centroidal SE(3) template

## 🔒 Key Constraints
- Read-only investigation — do NOT implement
- Write only to working directory: /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_controls_1
- No source code edits outside working directory
- .agents/teamwork/ must contain only metadata (no code/tests/data, no AGENTS.md or GEMINI.md)

## Current Parent
- Conversation ID: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Updated: 2026-10-19T05:23:00Z

## Investigation State
- **Explored paths**:
  - `docs/crossover-program-report-2026-10-18.md` and `docs/crossover-results-2026-10-18.md`
  - `lean/Research/ControlCertificates.lean`
  - `LeanForControl/README.md`
  - `ctrls/README.md`
  - `ctrl-research-notebook/research-notebook/publication/recovery-manuscript/main.tex`
  - Literature: Sleiman (2103.00946), van Wijk (2510.05436), Cohen-Molnar-Ames (2403.09865), Wu-Yi-Manchester (2403.15264), Franchi (2607.04719), PHRetune (2610.05755), Alfarano-Charton-Hayat (2410.08304)
- **Key findings**:
  - Seed 1 (Backup CBF + Lorentz Cone): Ranked #1. van Wijk (Oct 2025) solved box inputs; extending to Lorentz friction cone via straight-line interpolation between projected nominal input and backup controller yields an exact closed-form solution without solving a degree-4 polynomial.
  - Seed 2 (CCM on Underactuated SE(3)): Ranked #3. Monolithic closed-form CCM is obstructed by $SO(3)$ topology and unactuated horizontal acceleration cross-coupling (eigenvalues $\pm g$). Only cascaded/transverse formulation is tractable.
  - Seed 3 (IDA-PBC Contact + Drag): Ranked #2. Non-polynomial quadratic drag $\|v\| v$ breaks polynomial SOS, but backward synthesis with natural inertia shaping ($M_d = M$) eliminates the kinetic matching PDE and absorbs drag directly into $R_d(v)$, providing an exact closed-form solution.
- **Unexplored areas**: Formal Lean 4 code implementation of the candidate lemmas (deferred to subsequent implementation phase per read-only constraint).

## Key Decisions Made
- Prioritized Seed 1 as the primary candidate for the pod's R1/R2 push, followed by Seed 3 as the multi-physics target.
- Restricted Seed 2 to cascaded formulations to avoid topological/SOS dead-ends.
- Formulated exact mathematical falsification tests for all three seeds.

## Artifact Index
- DISPATCH.md — incoming instructions log
- BRIEFING.md — working memory and identity index
- progress.md — liveness heartbeat
- analysis.md — deep technical analysis of the 3 candidate seeds
- handoff.md — final 5-component report

