When plans change, how far can a robot stray?
Completed local proof-and-comparison artifact — 17 October 2026

Plain-language result

A smooth plan says where we want the axis to move. The real axis can lag behind.
We have now proved a bound on that difference for a scalar actuator model whose
response can change inside a known band. The same bound survives any finite
sequence of properly joined plans. The proof also gives extra space to leave
between a planned path and a travel limit.

Finished here

- TrackingReplan.lean: 20 checked statements. Derive the actual error ODE;
  establish the feedforward residual bound; preserve an error cube; connect
  the Bernstein reference admission test to actual travel/input margins;
  compose finite replans; distinguish two feedforward minimax objectives;
  bound actual jerk on each open segment.
- ScaledTracking.lean: 14 checked statements, including helper lemmas. Derive
  the physical time scaling by chain rule, then prove the scaled tube, physical
  margins and finite sequence result. Check the .2 mm example's exact budget.
- verification.json: passed. Fresh copies of the two targets and three local
  dependencies compiled. Every target statement passed the axiom audit. Both
  modules passed separate Lean kernel replay. Both deliberately false source
  changes were rejected: half the true interval residual, and reversed jerk
  feedforward with the original claimed error ODE.
- comparison.py: 144 deterministic cases, 288 integrations with tighter paired
  settings. This is numerical evidence. It is not an interval enclosure.
- review_numeric.py: independent exact parameter checks for all 144 cases and
  six independent RK4 integrations of the error ODE. Results are saved.
- challenge.txt: independent mathematical and claim review, including limits.
- ../../../publication/tracking-note/main.pdf: illustrated technical note.
- animation/changing-plans.mp4: 25-second Manim explanation, 1280 by 720 pixels.
  Its simulation is illustrative. It does not show measured robot behavior.

Exact physical contract

The scalar plant is x'=v, v'=a, a'=r(t)(u+w-a), with 8*sigma <= r <= 12*sigma.
The reference is q, q', q'', with planned jerk j. Let e be actual minus reference.
Use
  u=q''-8*sigma^2*e_x-6*sigma*e_v-e_a/2+5*j/(48*sigma).
The initial tilted error cube must satisfy
  |e_x|<=R,
  |e_x+e_v/(4*sigma)|<=R,
  |e_x+e_v/(2*sigma)+e_a/(16*sigma^2)|<=R.
Assume |w|<=W, |j|<=J, sigma>0, R>=0, and
  W+J/(48*sigma) <= 2*sigma^2*R.
Then the cube stays invariant and
  |x-q|<=R, |v-q'|<=8*sigma*R, |a-q''|<=64*sigma^2*R.
If |q''|<=A, the effective target obeys
  |u+w|<=A+24*sigma^2*R+5*J/(48*sigma)+W.
If q stays in [L+R,U-R], actual x stays in [L,U].

Each segment has a continuous state and an ODE on its open interior.
At every switch, match the old reference q/q'/q'' and keep the actual state.
Do not reset the reference to a measured actual state without a new bridge.
No lower dwell time is required for a finite sequence. Infinite/Zeno schedules
and derivatives exactly at jerk switches are outside this theorem.
The theorem is conditional on these trajectories. It does not prove existence
for arbitrary irregular rate or disturbance inputs.

Illustrative specification

sigma=10 requires an actual rate in [80,120]/s, roughly 8.3 to 12.5 ms lag.
W=.01 m/s^2, J=10 m/s^3 and R=.0002 m satisfy the budget.
This permits a .2 mm position tube if the initial cube and other assumptions hold.
The velocity margin is .016 m/s; the acceleration margin is 1.28 m/s^2.
The effective input margin above A is .594166... m/s^2.
These are specifications, not measured parameters. Raising gains on a slow
actuator does not make it satisfy this faster rate band.

Comparison finding

The coefficient 5/(48*sigma) minimizes the worst residual used by this cube.
The nominal coefficient 1/(10*sigma) minimizes the worst initial jerk error.
They solve different minimax problems. Neither is a universal tracking winner.
All three numerical competitors keep acceleration feedforward; one omits only
jerk feedforward. All use the same actual plant and reference in each paired case.

With W=.0005 m/s^2, take the largest sampled position error across four tested
rate signals. For the slow, short .16 mm move, omitting jerk feedforward gives
.11245 mm, nominal gives 1.88368 mm, midpoint gives 1.96018 mm. For the faster,
long 312.5 mm move, the respective values are .15642, .03176 and .02671 mm.
The short-move stress signal exposes a feedforward failure mode. The certificate
remains true but is very loose in that slow case. The full data retains this result.
The chosen varying-rate signal is not a proved worst-case adversary.

Reproduce from the research workspace root

  python3 research/adjacent-controls/tracking-replans/verify.py
  python3 research/adjacent-controls/tracking-replans/comparison.py
  python3 research/adjacent-controls/tracking-replans/review_numeric.py

Redraw without repeating integrations:
  .tools/travel-plot-python/bin/python research/adjacent-controls/tracking-replans/comparison.py --render

Render the animation with the existing pinned Docker image:
  research/adjacent-controls/tracking-replans/animation/render.sh

Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 are pinned.
The proof replay uses existing compiled LeanControls/Mathlib dependencies.
Source hashes and log hashes are in verification.json. Standard axioms are
propext, Classical.choice and Quot.sound. There are no added proof axioms or sorry.
Kernel replay checks the formal implication. It does not validate the model.
The numerical script requires numpy and scipy. Its optional figure rendering
uses the existing Matplotlib environment. No packages were installed for this run.

Done / open

Done: a checked finite-replan tracking result and a reproducible comparison.
Open: a sampled-controller implementation bridge; calibrated physical response
and error bounds; coupling/contact/flexible dynamics; persistent plan feasibility
and stop reserve; novelty assessment and external review for a chosen venue.
Planned jerk and actual jerk are different quantities. This is not a vibration-free
arm claim or a PL d/PL e reliability assessment. No paper was submitted.

The next useful task is to derive sampling, sensor and delay errors into W, then
compare against a measured or calibrated axis. Do that before adding another
unrelated mathematical branch. The current invariant can be conservative; a
finite-horizon bound is a separate candidate if precision is still inadequate.
