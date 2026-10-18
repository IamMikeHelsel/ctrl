A useful stopping bound under changing response
17 October 2026

Read index.html for the explanation, comparison and Manim video.

Main checked result
EventStop.delayed_event_first_stop proves a first velocity zero by 0.55 seconds
and position at most 0.15 metres at every time up to that event. Position is
relative to the measured starting reference. It is not displacement from the
unknown true starting position. There is no later holding guarantee.

Illustrative contract, SI units
- Initial position <= 0.001 m and true velocity in [0,0.41] m/s. The displayed
  example uses measured position zero ±1 mm and velocity 0.40 ±0.01 m/s.
- Delay D in [0,0.05] s. During delay, x'=v, v'=a and a<=0.1 m/s².
- After engagement and before the first true zero, x'=v, v'=a,
  a'=r(t)*(b(t)-a). Response rate r is continuous, in [8,12]/s.
  Effective acceleration target b<=-1.2 m/s² while the stop has not occurred.
- The actual state is continuous on [0,D+0.5]. The classical derivatives must
  satisfy the stated equations where required. This is a conditional guarantee
  for such trajectories, not a general existence theorem for arbitrary signals.
- The rate remains bounded/continuous across the horizon. Delay kinematics and
  its acceleration bound cover [0,D]. Braking ODE and target constraints stop
  at the first zero, so a different target can be selected at that event.

Files and proof roles
ComparisonEnvelope.lean: general scalar comparison and three-state envelopes
  for varying response rate and effective target; upper and lower bounds.
FirstStop.lean: existence of an earliest zero for a continuous velocity.
StoppingCertificate.lean: exact 0.15 m and 0.5 s post-engagement bounds, with
  an exponential inequality and delay-state arithmetic.
Counterexample.lean: an admitted slow/weak response, starting at the engagement
  state for the 0.50 m/s example, crosses the limit while still moving forward.
  Its request-to-engagement prefix is not formally composed in that module.
ActualStop.lean: actual delay integration, the initial stop theorem, and an
  explicit trajectory witness that makes the assumptions nonempty.
EventStop.lean: final event-limited theorem; no braking equation or negative
  target is required at the first zero or afterward.

Reproduce from the workspace root
  python3 research/adjacent-controls/variable-response/verify.py
  python3 research/adjacent-controls/variable-response/experiment.py
  sh research/adjacent-controls/variable-response/animation/render.sh

verify.py copies all six new sources into a fresh temporary directory, compiles
them, audits all 23 public named theorem closures, and runs leanchecker on every
module. Only propext, Classical.choice and Quot.sound are allowed. It also changes
the clearance claim to the false 0.10 m value and requires the proof to fail.
See verification.json for the actual status, hashes and log records. The pinned
LeanControls and mathlib build artifacts are reused. This is not a fresh build
of the entire proof stack or an independent verification of Lean itself.

experiment.py uses floating-point analytic evaluation and RK4 simulations. The
0.140711 m peak, 0.417341 m/s speed threshold and simulated traces are numerical
results. They are not the exact Lean certificate. The simple comparison bound
uses the same delay, state error, response-rate and strength assumptions.

Open work
The theorem concerns the true zero, not an implemented stop detector. Switching
early from a noisy velocity estimate can violate its braking premise. Sample
timing, ongoing state estimation, maintained rest, temperature/contact model
calibration, and a measured physical example remain open. A shoe losing and
regaining grip needs contact modes and a force law beyond this powered-axis
model. PL d/e needs a wider safety case. Novelty over existing robust stopping
and verified reachability methods is not established. The existing manuscript
has not yet been rewritten around this result.

The adjacent source-attribution example is an exact rational Python certificate,
not Lean. It has not been connected to this ODE model by a proved interface.
