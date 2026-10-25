## 2026-10-19T05:16:25Z
You are explorer_survey_controls_1.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_controls_1.
Write only to your working directory. Update progress.md regularly with timestamped progress.

CRITICAL INSTRUCTION:
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md before doing anything else.
Also read:
- /Users/mike/dev/ctrl/README.md
- /Users/mike/dev/ctrl/AGENTS.md (binding rules)
- /Users/mike/dev/ctrl/lean/Research/ControlCertificates.lean
- /Users/mike/dev/LeanForControl
- /Users/mike/dev/ctrls
- /Users/mike/dev/ctrl-research-notebook (control pods, recovery manuscript)

Your mission:
Deeply analyze Mike's candidate seeds on the 12-state centroidal SE(3) floating-base template (Sleiman et al. arXiv:2103.00946):
1. Closed-form backup CBF with a Lorentz friction-cone input set (cf. van Wijk et al. arXiv:2510.05436 for box inputs; Cohen–Molnar–Ames arXiv:2403.09865).
2. Closed-form control contraction metric on underactuated SE(3) (cf. Wu–Yi–Manchester arXiv:2403.15264; Manchester–Slotine arXiv:1503.03144).
3. Closed-form IDA-PBC energy-shaping solutions for coupled contact + drag on a floating base (cf. arXiv:2607.04719, arXiv:2610.05755), possibly via backward synthesis (arXiv:2410.08304).

For each seed:
1. Verify open claims against recent literature (2024-2026) using web search or literature search.
2. Evaluate feasibility of symbolic search + fast verifiers / backward synthesis vs polynomial SOS.
3. Define exact verification pathways: symbolic computation, exact/interval arithmetic, and formal Lean certificate in ControlCertificates.lean.
4. Design a concrete falsification test to rapidly reject unviable candidates.
5. Rank the candidates by tractability and impact.

Deliver your complete findings in /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_controls_1/handoff.md.
When finished, send a message to the caller with the path to your handoff.md and a concise summary.
