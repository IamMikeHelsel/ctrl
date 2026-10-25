# BRIEFING — 2026-10-19T05:24:00Z

## Mission
Survey and triage open math problems across repos to identify 2-3 candidate open problems in math/combinatorics/discrete math where computational/symbolic or cross-discipline methods could yield a new checkable result or certificate.

## 🔒 My Identity
- Archetype: explorer
- Roles: survey, triage, cross-discipline synthesis
- Working directory: /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_math_1
- Original parent: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Milestone: survey_and_triage_completed

## 🔒 Key Constraints
- Read-only investigation — do NOT implement
- Write ONLY to /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_math_1
- No challenge statements edited, no human approvals fabricated, development mode (AGENTS.md binding integrity rules)
- Erdős 834 was claimed upstream — treat as pilot/reference, NOT novelty target

## Current Parent
- Conversation ID: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Updated: not yet

## Investigation State
- **Explored paths**:
  - `ORIGINAL_REQUEST.md`, `README.md`, `AGENTS.md`, `docs/crossover-program-report-2026-10-18.md`, `docs/targets.md`, `docs/next-target-program-report-2026-10-18.md`, `docs/architecture.md`, `docs/machines.md`
  - `work/834/` (status.json, plan.md, crossover certs)
  - `data/erdos/open.csv`, `data/erdos/formalize.csv`
  - Sibling repos: `ctrl-erdos-rename` (tools/ctrl_cli/triage.py, tools/data/plby_erdos.json, awards_prs.json), `ctrl-erdos-lab` (Challenge/ and ErdosLab/ for 261, 291, 382, 834, 931)
  - Reference Formal Conjectures: `~/Dev/formal-conjectures` (97.lean, 86.lean, 273.lean, 500.lean, 556.lean, 99.lean, 143.lean)
- **Key findings**:
  - Erdős 834 verified in `plby_erdos.json` (line 426) as claimed upstream; serves as pilot/reference for SAT/NAE tree compression, not a novelty target.
  - Surveyed 642 open problems in `data/erdos/open.csv`, checking against recent literature (noting Jeong et al. arXiv:2609.27495 on Erdős 500).
  - Selected and detailed top 3 candidate open problems:
    1. Erdős 86 ($100 prize): Hypercube $C_4$-free Turán density $\pi_Q(C_4)$ via Flag Algebras + SDP on Spark -> rational SOS certificate in Lean.
    2. Erdős 97 ($100 prize): Convex polygons with 4 equidistant vertices via Real Algebraic Geometry & Vision Minimal Solvers (homotopy continuation, Cayley-Menger varieties) -> exact rational coordinates in Lean.
    3. Erdős 273 (Open): Restricted covering systems with moduli $p-1$ ($p \ge 5$) via Lyapunov-like potential functions (Local Cut Lemma) + SAT solving (Kissat/CaDiCaL on Spark) -> finite covering witness or LRAT UNSAT proof.
- **Unexplored areas**: None. Handoff report finalized in `handoff.md`.

## Key Decisions Made
- Concluded investigation and produced complete 5-component report in `handoff.md`.

## Artifact Index
- DISPATCH.md — Incoming dispatch message log
- BRIEFING.md — Persistent situational awareness
- progress.md — Liveness heartbeat and milestone tracking
- handoff.md — Final 5-component report
