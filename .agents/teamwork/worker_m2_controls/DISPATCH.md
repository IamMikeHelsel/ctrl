## 2026-10-19T05:30:09Z

You are worker_m2_controls.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_m2_controls.
Write your notes, progress, and handoff to your working directory. Update progress.md regularly with timestamped progress.

CRITICAL INSTRUCTION:
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md before doing anything else.
Also read:
- /Users/mike/dev/ctrl/PROJECT.md
- /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_controls_1/handoff.md
- /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_controls_1/analysis.md
- /Users/mike/dev/ctrl/lean/Research/ControlCertificates.lean

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Your assigned scope (Milestone 2: Controls — Seed 1 Centroidal Lorentz-Cone Backup CBF):
1. Exclusive write ownership:
   - `/Users/mike/dev/ctrl/lean/Research/LorentzConeCBF.lean`
   - `/Users/mike/dev/ctrl/tools/verify_lorentz_cbf.py`
   - `/Users/mike/dev/ctrl/tests/test_lorentz_cbf.py`
   Do NOT touch any other source or test files. Sibling repos are strictly read-only.
2. Implement `lean/Research/LorentzConeCBF.lean`:
   - Define Lorentz friction cone constraint $\mathcal{K} = \{ u \in \mathbb{R}^3 \mid u_1^2 + u_2^2 \le \mu^2 u_3^2, u_3 \ge 0 \}$.
   - Prove convexity of $\mathcal{K}$ (or convex combination invariance: if $u_1, u_2 \in \mathcal{K}$ and $\lambda \in [0, 1]$, $(1-\lambda) u_1 + \lambda u_2 \in \mathcal{K}$).
   - Define stopping-distance backup CBF $h_b(r, v) = (r_{\text{limit}} - r) \cdot \hat{n} - \frac{\|v\|^2}{2 a_{\text{brake}}}$.
   - Formalize the closed-form interpolation controller $\lambda^*(x) = \max\left(0, \frac{b(x) - a(x)^\top \bar{u}_{\text{nom}}}{a(x)^\top \pi_b(x) - a(x)^\top \bar{u}_{\text{nom}}}\right)$ and prove it satisfies the CBF condition and stays inside $\mathcal{K}$.
   - Build cleanly with `cd /Users/mike/dev/ctrl/lean && lake env lean Research/LorentzConeCBF.lean`. Must have 0 `sorry` and depend ONLY on standard axioms `[propext, Classical.choice, Quot.sound]`.
3. Implement `tools/verify_lorentz_cbf.py`:
   - Exact symbolic verification (via sympy / exact fractions) of the Lie derivatives $\dot{h}$ and the defining barrier inequality over the continuous domain.
   - Exact/interval arithmetic verification over an operating box envelope.
   - Concrete falsification checks: friction limit $\|a_{\text{brake}}\| \le \mu g$ and ZMP support polygon boundary check.
4. Implement `tests/test_lorentz_cbf.py`:
   - Test suite verifying exact symbolic properties, convex interpolation validity, and friction cone admissibility across diverse test cases.
   - Run `cd /Users/mike/dev/ctrl && uv run pytest tests/test_lorentz_cbf.py` and ensure 100% pass.
   - Run full test suite `uv run pytest -q` to guarantee zero regressions.
5. Deliver complete report in `/Users/mike/dev/ctrl/.agents/teamwork/worker_m2_controls/handoff.md`.
When complete, notify caller via `send_message`.
