SIX NUMERICAL COMPARISON EXAMPLES

These examples show where the fixed negative recovery command helps a little,
wastes effort, or fails. They do not prove safety, optimality, or a general
advantage for either controller.

Run from the workspace root:
  .tools/research-python/bin/python research/adjacent-controls/comparison-examples/examples.py

Files:
  examples.py - preselected cases, computation, and SVG generator
  results.json - conditions, source hashes, full metrics, and sampled traces
  comparison.svg - six-panel contact sheet with common position/time scales
  run.log - numerical summary from the saved run

Model and comparison:
  x'=v, v'=a, a'=r(u-a), with fixed r and no errors.
  Direct feedback samples clip(-x-3v-2a) every h=0.05.
  Backup holds u=-1 until T=1.25, then uses the same sampled feedback.
  T is on the direct sample grid, so the post-T sample times match.
  Horizon: 10 normalized time units. There are no physical units or hardware
  calibration. All initial cases and rates were fixed before computing results.

The held-flow formula, command, energy, and numerical extrema code are imported
unchanged from ../recovery-proof/experiment.py. The direct-comparison interval
prototype models the same equations but is not used for this numerical study.
No parameter search or new package installation was performed.

Observed results (direct / backup):
  At rest at target, z=(0,0,0), r=1:
    Peak |x|: 0 / 1.269. Integral |u|: 0 / 3.657.
    Applying this backup without a guard creates needless motion.
  Slow case, z=(0.5,0.05,0), r=1:
    Peak |x|: 0.515 / 0.637. Terminal V: 0.925 / 17.904.
    Integral |u|: 0.463 / 3.112. Direct feedback is better on these metrics.
  Nominal case, z=(1,0.5,0), r=1:
    Peak |x|: 1.3832 / 1.3812. Terminal V: 10.154 / 10.092.
    Integral |u|: 1.708 / 1.999. Backup gives a small travel reduction and
    slightly lower terminal V, with more command effort and variation.
  Motion toward target, z=(1,-0.5,0), r=1:
    Peak |x|: 1.000 / 2.054. The unguarded negative backup passes the negative
    travel limit numerically. This case is outside the proved recovery box.
  Faster case, z=(1,0.9,0.2), r=0.9:
    Both peak near 2.230 and exceed the travel limit numerically.
  Fast case closer to limit, z=(1.5,1,0.3), r=0.9:
    Both peak near 3.076 and exceed the travel limit numerically.
    In these numerical runs, the direct controller already selects the same
    saturated command during the backup phase; the backup adds no benefit.

Interpretation:
Use the proved recovery condition as a guard. Do not apply a fixed negative
command merely because the controller is called a brake. Its direction can
oppose or aid the current motion. The current nominal case has only a small
performance benefit; its stronger contribution is the checked model-to-proof
handoff. These cases also make clear that neither policy can rescue every
initial position, velocity, and acceleration under the same actuator limit.

Evidence limits:
Peak travel is obtained from analytic segment formulas with numerical velocity
root bisection, not certified outward-rounded bounds. Energy peaks are sampled
at spacing at most 0.01. Terminal V is evaluated at exactly T for both policies.
Command variation excludes a jump from an unspecified command before time 0.
The command integral is an effort proxy; it is not mechanical or electrical
energy. Only the nominal center lies in the small initial box covered by the
existing recovery theorem. The other cases neither refute that theorem nor
establish new ones. The SVG uses a common position range [-4,4]; its ±2 lines
show the same normalized travel limits in every panel.

Rendering note:
The first SVG attempt used a [-3,3] plot range and stopped when the near-limit
case exceeded it. Only the common display range changed to [-4,4]; cases and
controller parameters stayed fixed. Later formatting aligned the metric columns.
