RECOVERY AND HANDOFF — CONCRETE CHECKED CASE STUDY
17 October 2026. Local research artifact; no external submission.

Result
------
For x'=v, v'=a, a'=r(u-a), with one fixed r in [0.9,1.1], start in
  x in [0.99,1.01], v in [0.49,0.51], a in [-0.01,0.01].
Hold exactly u=-1 until normalized time 1.25, then start the existing
sampled saturated feedback -x-3v-2a, with no state reset.

After handoff, some hmin>0 must satisfy hmin<=h_n<=0.2, and held request/drive
errors obey |e_n|+|d_n|<=1/90. The drive error is inside the rate multiplier.
The backup has zero disturbance and an exact switch time. The same fixed r
is used throughout both phases.

Every initial state is outside the old energy region V<=12 (V>=23.498378).
The full backup path has x in [657/800,5297/3200], and the full terminal state
has V<=12. Every continuous execution of the stated own-feedback ODE then
satisfies |x(t)|<=2 for all t>=0. Such executions exist and are unique on
nonnegative time for the same prescribed parameters and error sequences.

The physical counterpart uses r=tau0/tau, scaling
z=(X/(U*tau0^2), velocity/(U*tau0), acceleration/U), backup command -U,
switch time 5*tau0/4, later holds <=tau0/5 and error budget U/90. It proves
|X(s)|<=2*U*tau0^2 for every nonnegative physical time. No hardware calibration
or finite-word implementation correspondence is claimed.

Files
-----
RecoveryPath.lean: transient derivative bounds and initial exclusion.
TerminalBase.lean: exponential-point enclosure and energy LDL identity.
TerminalCells.lean: 33 exponential endpoint certificates, 32 closed rate cells,
  direct full-initial-box energy evaluation, complete terminal theorem.
RecoveryHandoff.lean: actual switched ODE, time shift, continuity, existence,
  uniqueness and generic certificate transfer.
RecoveryBox.lean: concrete normalized theorem with safety premises discharged.
PhysicalRecovery.lean / PhysicalRecoveryBox.lean: physical normalization,
  existence, uniqueness, concrete physical travel and terminal entry.
generate_terminal.py: untrusted rational producer; --check compares output.
verify.py: fresh source rebuild, all-theorem axiom audit, individual kernel
  replay, and a rejected terminal-time/model-identity mutation.
verification.json and verification-logs/: current complete check evidence.
verification-first-attempt*: retained bootstrap failure (checker could not
  locate the toolchain on PATH); fixed before the successful final replay.
terminal-first-attempt.log: retained interval-tactic elaboration failure.
experiment.py / experiment-results.json / experiment-review.txt: numerical
  matched comparisons, explicitly separate from the universal theorem.
adversarial-review.txt: independent agent challenge of the semantic contract.

Reproduce in the workspace
--------------------------
From the workspace root:
  python3 research/adjacent-controls/recovery-proof/generate_terminal.py --check
  python3 research/adjacent-controls/recovery-proof/verify.py
  python3 research/adjacent-controls/recovery-proof/experiment.py

verify.py prefers .tools/elan/bin/lake when present, otherwise lake on PATH.
An explicit executable can be selected with RECOVERY_LAKE. Python uses only
the standard library for this extension. The pinned toolchain is Lean 4.35.0,
mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679.

Prerequisite: the adjacent lean-controls/ base project must have its pinned
dependencies and compiled base modules. To provision that base on a new
machine with elan/lake installed, keep the included lean-toolchain and
lake-manifest.json, then from lean-controls run:
  lake exe cache get
  lake build
The Mathlib interval tactic dependency can be fetched explicitly if needed:
  lake exe cache get Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
The old base's scripts/verify_project.py additionally regenerates and checks
its own rational control certificates and mutations (requires its Python
requirements). The new check does not substitute for that base verification.

verify.py copies all seven recovery sources into a fresh temporary directory,
builds them without original recovery oleans, audits 98 named theorems, and
replays each resulting module with leanchecker. It trusts the pinned Lean
executable and the preexisting base/mathlib dependencies. It is not an
independent bootstrap of Lean or a fresh rebuild of all mathlib sources.
Only propext, Classical.choice and Quot.sound are allowed in theorem closures.
No native_decide/compiler-trust axiom is used. The finite interval computation
uses dyadic_interval with native=false. Logs preserve the actual commands.

Interpretation and publication
------------------------------
The theorem extends certified starting states; it does not establish that
direct feedback is unsafe on the new box. All 24 tested direct-feedback runs
also stayed within the limit and entered the old ellipsoid. Recovery's small
travel improvement is accompanied by mixed terminal-energy outcomes and
greater command variation. The combined one-time initial-state mode selector
is a mathematical design consequence, not a verified implementation.

The prior diagnostic's bound below 11.235 is not the Lean theorem's exported
bound. The proved terminal bound is V<=12. The initial box is small and selected,
not maximal. Backup disturbance, switch jitter, finite arithmetic, friction,
state estimation and coupled-axis behavior remain open extensions.

Paper: ../../../publication/recovery-manuscript/main.pdf
Animation: ../recovery-animation/recovery-proof.mp4
Public-facing animation source and pinned Docker render command are beside it.
Academic pretty-print tools: ../../academic-tools/pretty-math.html

Next publication gate: matched direct-prefix certification and outside human
review of usefulness and novelty. Backup control and formal control-envelope
pipelines have prior art; neither the method name nor theorem count is a claim
of new control theory. The original base manuscript/archive remains frozen.
