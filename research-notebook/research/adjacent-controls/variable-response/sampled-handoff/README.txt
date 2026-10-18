Stopping is only half the job
17 October 2026

New result
We can accept a noisy full-state reading, allow up to 5 ms of command delay,
and switch continuously into an actual feedback law that keeps position in a
certified region. This is bounded-position holding. Exact rest and convergence
are not conclusions, especially with a persistent target error.

The final theorem starts at the state reading. It does not yet compose the
original stop-request trajectory, a sample schedule, eventual detector acceptance,
and this holding trajectory into one execution theorem.

Illustrative admission
Reading: x=0.14 m, v=-0.01 m/s, a=-1.17 m/s².
Measurement errors: ±0.001 m, ±0.01 m/s, ±0.05 m/s².
Actual delay d: anywhere in [0,0.005] s.
During delay: x'=v, v'=a, |a|<=2 m/s², |a'|<=48 m/s³.
No coordinate is reset when the holding command takes effect.

The admitted holding reference is c=141/1600 m = 8.8125 cm.
Its radius is R=2221/40000 m = 5.5525 cm.
For any horizon on which the actual holding model holds, position stays in
[c-R,c+R] = [0.0326,0.14365] m, inside the original [0,0.15] m travel range.
The controller can deliberately retreat toward c. This is not precision rest
at the measured 14 cm position.

Holding model
  x'=v, v'=a, a'=r(t)*(u+w(t)-a)
  u=-8*(x-c)-6*v-a/2
  r(t) in [8,12]/s, |w(t)|<=2R = 0.11105 m/s².

The numerical coefficients have the SI units implied by this acceleration
command. w is an additive acceleration-target error inside the rate multiplier.
It is not an external jerk. The proof derives transformed coordinates
  z=(x-c, x-c+v/4, x-c+v/2+a/16)
from the actual differential equations. The cube |zi|<=R is invariant.
It also proves |u|<=24R=1.3326 m/s² and |u+w|<=26R=1.44365 m/s²,
which fit an illustrative effective-target authority of ±2 m/s².

This law uses continuous actual-state feedback. A digital controller has sample
age, sensor error and held-command mismatch. Those errors must be derived and
shown to fit w before this theorem certifies that implementation. A generic
existence theorem for all bounded rough signals is not asserted. The result
applies to actual classical trajectories satisfying the ODE. An equilibrium
witness shows that the hold assumptions are nonempty.

Proof files
Capture.lean: state-error growth during delay; a measured threshold-crossing
velocity bound; transformed measurement intervals; exact concrete admission.
RobustHold.lean: finite first-contact lemma, actual ODE transformation, robust
invariant cube, physical bounds and zero-velocity capture geometry.
ReleaseCounterexample.lean: an actual zero-target lag trajectory, starting with
exactly zero velocity, eventually crosses every finite rear limit.
Handoff.lean: combines the noisy reading, bounded delay, exact full-state handoff
and arbitrary-horizon holding bounds.

Verification
20 public named theorem statements passed fresh source compilation, transitive
axiom audits and individual kernel replay. Four local dependency sources were
also rebuilt. Pinned LeanControls/mathlib artifacts were reused. Only propext,
Classical.choice and Quot.sound occur. A false 14 cm tube claim is rejected.
See verification.json and verification-logs/ for exact source and log hashes.

Reproduce from the workspace root
  python3 research/adjacent-controls/variable-response/sampled-handoff/verify.py
  python3 research/adjacent-controls/variable-response/sampled-handoff/experiment.py
  sh research/adjacent-controls/variable-response/sampled-handoff/animation/render.sh

Numerical evidence
The prior weak/slow braking trajectory at request time 0.53 s is consistent with
the fixed noisy reading. It continues braking through the illustrative 5 ms
delay. The exact starting state is preserved at the controller switch. We then
simulate fixed-rate holding, changing-rate holding with target error, and naive
zero-target release. Step refinement checks numerical stability; the simulation
does not replace the proof. Reachability of this reading from the original
request is numerical evidence only in this batch.

With the same reading and errors, a 20 ms delay gives a wider proposed tube and
an effective-target bound above 2. Our exact rational admission calculation
rejects it. A rejected sufficient certificate does not establish unsafe motion.

Next useful connection
The VLA work in ../../vla-smooth-replanning proves a separate command-level
smoothness certificate. A useful combined contract would admit a new segment
only when it is smooth, respects uncertainty, and retains a certified stopping
or holding fallback. The planner-to-plant connection is still unproved.
Physical calibration, a matched public benchmark and research novelty remain
open. No hardware, ISO 13849 PL d/e, or full dexterous-robot claim is made.
