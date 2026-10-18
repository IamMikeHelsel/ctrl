STEADY ENOUGH TO MOVE
17 October 2026

Open index.html for the evidence, theorem scope, comparison, and Manim video.

What is checked
- CommitmentGate.lean: bounded-noise target rejection; response threshold;
  target error; finite accepted-target variation/count; stale proposal error;
  scalar recentering; a common-observation ambiguity witness.
- QuietHold.lean: the actual lagged plant uses the time-indexed gated reference.
  Under fixed intended target and valid bounded-noise proposals, Lean derives
  that this reference stays fixed, then proves physical error <= R+epsilon
  and effective acceleration-target magnitude <= U under the declared premises.
- 16 public theorem statements pass fresh compilation, transitive axiom audit
  and standalone kernel replay. Only propext, Classical.choice and Quot.sound
  occur. The two local dependency sources are rebuilt; pinned LeanControls
  and mathlib artifacts are reused.
- A mutation that changes the illustrative target-variation factor from 2 to 1
  is rejected. It is false: an accepted move from -0.5 mm to 1.6 mm has length
  2.1 mm while true targets can move from 0 to 1.1 mm. Both proposal errors are
  0.5 mm and the accepted step exceeds the 2 mm threshold.

Reproduce from this workspace root
  python3 research/adjacent-controls/steady-motion/verify.py
  python3 research/adjacent-controls/steady-motion/experiment.py

The verifier uses the existing pinned Lean 4.35.0 / mathlib environment in
lean-controls and .tools/elan. It builds copied source in a fresh temporary
folder, records source and log hashes, and checks that source did not change.
See verification.json, verification-logs/, and theorem-challenge.txt.
The first proof drafts were not the final verified sources; the final hashes
are recorded in verification.json and in the independent review.

The target-layer experiment uses the Python standard library. Truth, bounded
noise, dwell, and the gate use exact fractions. The one-pole filter uses floats.
It compares four scenarios at 50, 100 and 200 Hz. The independent critic replayed
all 12 scenario/cadence pairs. Different cadences change the alternating-noise
frequency. This is an illustration of decisions and aliasing, not a ranking
on one continuous physical disturbance.

What remains open
- A bound on real VLA proposal error at execution time, including stale scenes.
- Formal extraction of the accepted-index history used by the variation bound.
- Physical tracking during useful changing-target motion, with sensor errors,
  sampled feedback, delay, saturation, flexible modes, and contact.
- Smooth feasible transitions that retain the stopping/holding reserve.
- A useful precision radius on a measured robot. The older 55.525 mm radius
  was a travel-safety example, not precision holding.
- Novelty and a demonstrated advantage over established reference governors,
  variable-impedance control, disturbance observers and continuation methods.

The physical theorem permits motion inside a tube. It does not prove zero
vibration, velocity convergence, grip stability, or task progress. Gate target
variation is not physical path length. A safety rejection can keep an older
reference, so the gate's selected-target error theorem cannot silently be
applied after a downstream rejection.

Human studies motivate engineering hypotheses. They neither identify a single
cause of tremor nor prove that humans use this threshold rule. Source access
and limits are in sources-neuro.json and sources-controls.json.

The animation is a public explanation of target decisions. It is not a robot
simulation. See animation/README.txt for the pinned Docker render and provenance.
Nothing has been submitted or published. No robot or VLA ran in this batch.
