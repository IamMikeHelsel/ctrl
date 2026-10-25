## 2026-10-19T06:35:38Z
You are worker_m5_push.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_m5_push.
Write your notes, progress, and handoff to your working directory. Update progress.md regularly with timestamped progress.

CRITICAL INSTRUCTION:
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md before doing anything else.
Also read:
- /Users/mike/dev/ctrl/PROJECT.md
- /Users/mike/dev/ctrl/.agents/teamwork/orchestrator_1/GATE_STATUS.md
- /Users/mike/dev/ctrl/lean/Research/LorentzConeCBF.lean
- /Users/mike/dev/ctrl/lean/Research/HomographyDecomposition.lean
- /Users/mike/dev/ctrl/tools/sdp_rational_cert.py
- /Users/mike/dev/ctrl/tests/test_sdp_rational_cert.py

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

MANDATORY HYPOTHESIS AUDIT RULE (Parent Directive 2026-10-19T06:17:41Z):
List every hypothesis and structure field in your theorems. Verify that NO hypothesis encodes the crux of the claimed result. Any theorem whose crux is an assumed hypothesis is capped at 'scaffolding', regardless of zero-sorry status. Do not introduce trivia (e.g. 2+6=8). A smaller theorem with NO smuggled crux strictly beats a large file of bookkeeping. The crux MUST be proven from first principles.

Your assigned scope (Milestone 5: R2 Cross-Discipline Push on Open Targets):
1. Exclusive write ownership:
   - `/Users/mike/dev/ctrl/lean/Research/CentroidalDecelerationLimit.lean`
   - `/Users/mike/dev/ctrl/lean/Research/VisualServoingInvariant.lean`
   - `/Users/mike/dev/ctrl/tools/run_lane_sdp_cert.py` (or `/Users/mike/dev/ctrl/tools/push_sdp_cert.py`)
   - `/Users/mike/dev/ctrl/tests/test_crossover_push.py`
   Do NOT touch any other source or test files. Sibling repos are strictly read-only.

2. Push B (Controls — Deceleration Limit & Exact Counterexample Theorem):
   In `/Users/mike/dev/ctrl/lean/Research/CentroidalDecelerationLimit.lean`:
   Formulate the exact physical braking limit $a_{\text{safe}}^{\max} = g \min(\mu, W / h_G)$ from friction coefficient $\mu > 0$, support half-width $W > 0$, COM height $h_G > 0$, and gravity $g > 0$.
   Prove two complementary headline theorems:
   (i) Positive Theorem (`deceleration_safe_unconditional`): For any required deceleration $a_{\text{req}} \le a_{\text{safe}}^{\max}$, the friction cone constraint ($|a_{\text{req}}| \le \mu g$) AND the ZMP zero-moment-point tipping constraint ($h_G |a_{\text{req}}| / g \le W$) are UNCONDITIONALLY satisfied, with ZERO assumed $h_{\text{margin}}$ or slack hypothesis!
   (ii) Negative Counterexample Theorem (`deceleration_unsafe_counterexample`): For any $a_{\text{req}} > a_{\text{safe}}^{\max}$, either slip ($|a_{\text{req}}| > \mu g$) OR rotational tipping ($h_G |a_{\text{req}}| / g > W$) is mathematically inevitable.
   Must compile cleanly with `cd /Users/mike/dev/ctrl/lean && lake env lean Research/CentroidalDecelerationLimit.lean` (exit code 0, 0 sorry, standard axioms `[propext, Classical.choice, Quot.sound]`).

3. Push C (Vision -> Controls — Visual Servoing Depth Invariance):
   In `/Users/mike/dev/ctrl/lean/Research/VisualServoingInvariant.lean`:
   Model closed-loop camera-frame position kinematics under homography-based visual servoing velocity command $\dot{X}_c(t) = -\lambda (X_c(t) - X_c^*)$ with gain $\lambda > 0$.
   Prove that along any trajectory satisfying this closed-loop law, the camera-frame depth along the plane normal $n$ satisfies:
   $n \cdot X_c(t) = e^{-\lambda t} (n \cdot X_c(0)) + (1 - e^{-\lambda t}) (n \cdot X_c^*)$.
   Prove the Invariant Theorem (`visual_servoing_depth_positive`):
   If initial depth $n \cdot X_c(0) > 0$ and target depth $n \cdot X_c^* > 0$, then for all $t \ge 0$, $n \cdot X_c(t) \ge \min(n \cdot X_c(0), n \cdot X_c^*) > 0$ unconditionally, with ZERO assumed margin hypothesis!
   Must compile cleanly with `cd /Users/mike/dev/ctrl/lean && lake env lean Research/VisualServoingInvariant.lean` (exit code 0, 0 sorry, standard axioms `[propext, Classical.choice, Quot.sound]`).

4. Push A (Math — Exact Rational Dual SDP Certificate on Active Lane):
   In `/Users/mike/dev/ctrl/tools/push_sdp_cert.py`:
   Apply the exact rational dual SDP certificate pipeline (`tools/sdp_rational_cert.py`) to an active problem target in the repo (such as certifying the Lyapunov operator positive definiteness bound from `work/pod/mf13/opt/lyap.py`, or certifying the discrete energy bound on the $6 \times 4$ grid / 2x2 block trace in `work/pod/885/`, or the Erdős 834 hypergraph certificate).
   Verify that the rational certificate $S_{\mathbb{Q}} = L D L^\top \succ 0$ holds exactly over $\mathbb{Q}$ with all $D_i > 0$.

5. Python Unit Test Suite:
   Implement `/Users/mike/dev/ctrl/tests/test_crossover_push.py`:
   - Test `CentroidalDecelerationLimit` positive safety bound and negative counterexample threshold across diverse physical parameters ($\mu, W, h_G, g$).
   - Test `VisualServoingInvariant` exponential depth evolution and positive depth lower bound.
   - Test `push_sdp_cert.py` exact rational factorization and certificate verification.
   - Ensure 100% pass rate: `cd /Users/mike/dev/ctrl && uv run pytest -v tests/test_crossover_push.py`.
   - Ensure zero regressions on full project test suite: `uv run pytest -q`.
   - Ensure clean linter: `uv run ruff check`.

6. Reporting:
   Deliver your complete handoff report to `/Users/mike/dev/ctrl/.agents/teamwork/worker_m5_push/handoff.md`.
   Include full Hypothesis Audit table for every Lean theorem, exact verification commands, outputs, and evidence tiers.
   When complete, send a message to caller with the path to your handoff.md.


## 2026-10-19T06:37:48Z
[Message from 0b6a5e14-8c10-4497-8beb-fd637698bacb]
**Context**: Milestone 5: Critical Calibration & Directives from Parent Orchestrator.
**Content**:
Please read this guidance immediately before sinking effort into M5 implementations:

1. **Push B (Controls — Deceleration Limit & Joint Friction/Tipping)**:
   - Note that $a_{\max} = g \cdot \min(\mu, W/h_G)$ is the textbook friction/tip-over (ZMP) braking limit for a rigid body on flat ground. A kernel-checked proof is a valuable artifact, but must be explicitly labeled **"formalization of known result" (or candidate/scaffolding)**, not new.
   - Make it substantive:
     - State the physical model explicitly: rigid body, flat ground, support polygon $[-W, W]$, constant COM height $h_G$, contact normal forces $f_{z,1}, f_{z,2} \ge 0$.
     - Address the joint 3D Lorentz cone coupling: when lateral acceleration $a_y \ne 0$ is present, friction along braking axis $x$ is reduced by the circular Lorentz cone constraint $a_x^2 + a_y^2 \le \mu^2 (g + a_z)^2 \implies |a_x| \le \sqrt{\mu^2 (g + a_z)^2 - a_y^2}$.
     - Prove the exact positive theorem and the exact negative counterexample theorem (inevitable slip or tipping for $a > a_{\max}$).

2. **Push C (Vision → Controls — Visual Servoing Depth Invariance & Chaumette's Conundrum)**:
   - Parent warning: "Positive depth preserved for all $t \ge 0$ unconditionally" is generally FALSE for classic homography-based visual servoing due to **camera retreat (Chaumette's conundrum)**, feature loss, or rotational singularities.
   - Treat "unconditionally" as a red flag.
   - Formulate the problem rigorously:
     - (Option 1): Explicitly identify and formalize the classic camera retreat phenomenon as an exact counterexample (e.g. pure rotation about optical axis causing translational retreat $Z \to \infty$ or $Z \to 0$ under standard unconstrained interaction matrix).
     - (Option 2): Formalize the 2.5D visual servoing law (Malis, Chaumette, Boudet) or decoupled control law that incorporates a depth barrier certificate or explicitly proven positive-depth invariant under stated conditions ($n \cdot X(0) > 0$, $n \cdot X^* > 0$, and bounded rotational error).
     - A clean counterexample trajectory showing Chaumette camera retreat PLUS a kernel-checked conditional barrier theorem is a far better and more publishable scientific result than an oversimplified toy model.

3. **Push A (Math — Active Lane SDP Certification)**:
   - Clearly identify the specific target being certified (e.g., in `work/pod/mf13/` for Lyapunov operator SOS certificates, `work/pod/885/` for the $6 \times 4$ grid / 2x2 block trace bounds, or elevating the Erdős 834 hypergraph numerical bound $44.5189$ to the exact rational certificate $44.5279$).
   - Explicitly articulate what the certificate establishes: does it prove an exact rational dual bound over $\mathbb{Q}$ that eliminates floating-point solver error, and how does it compare to prior literature bounds?

**Action**: Calibrate `CentroidalDecelerationLimit.lean`, `VisualServoingInvariant.lean`, `push_sdp_cert.py`, and `tests/test_crossover_push.py` to meet these standards. Include the hypothesis audit in your handoff report.
