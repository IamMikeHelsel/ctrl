TWO ROUTES TO THE SAME SAFE REGION
Comparison record, 17 October 2026

The result
Direct feedback passes a rational interval calculation over the whole original
initial box and lag range. This is stronger evidence than the earlier corner
tests. The computation is not checked in Lean. The recovery theorem remains
the complete formal safety result.

The common comparison contract
  x'=v, v'=a, a'=r(u-a), with one fixed r in [.9,1.1].
  Initial box: [.99,1.01] x [.49,.51] x [-.01,.01].
  Both prefixes have zero errors and finish at T=1.25.
  Direct feedback: 25 holds of .05, u=clip(-x-3v-2a,-1,1).
  Brake: u=-1 throughout the prefix, split into 25 holds for comparison.
  Position target throughout the prefix: |x|<=2.
  Terminal target: V<=12, using the existing exact matrix P.
The same robust sampled contract can start at T. The direct actual-execution
composition remains open. No tail is simulated by the family scripts. The
coarse plan's phrase "zero in both phases" refers only to its tested prefixes;
it must not be read as a result about the tail.

Computed evidence
The original direct run covers 1,024 closed parameter boxes. Its terminal
energy bound is below 11.464. The entire prefix lies within [.9887,1.4310].
These displayed bounds round outward. Exact fractions are in the JSON trace.
No floating-point calculation decides whether an enclosure passes.

We fixed four nested boxes before the family runs. Their center is (1,.5,0),
and each coordinate has halfwidth lambda/100, for lambda in {1,2,4,8}.
The initial-state volume is (lambda/50)^3. It is not a probability.

The first partition has 4 subdivisions per state coordinate and 16 rate cells.
One uniform refinement has 8 subdivisions per coordinate and 32 rate cells.
Both policies use each partition for every selected region. There was no
further tuning. Refined upper bounds, rounded upward:

  lambda     direct V       brake V       position test
    1          11.380        11.087          both pass
    2          12.036        11.714          both pass
    4          13.467        13.131          both pass
    8          16.815        16.611          both pass

The terminal threshold is 12. The brake passes on the scale-2 box; the direct
enclosure does not. This is a certificate-method outcome. It does not prove
a larger true safe region. Direct feedback's scale-2 bound fell from 12.166
to 12.036 with refinement. Selected trajectories stay below 12. Interval
overestimation can explain a failed test. A failed terminal test also does
not establish a position-limit violation.

What Lean checked
DirectSwitch.lean proves that the nominal sampled controller releases full
braking at t=.8 while V>12. Its initial state is (1,.5,0), its rate is 1, and
its hold is .1. The command is then -49/50. Thus the release sample does not satisfy the invariant theorem's entry
premise. This module does not prove that no earlier entry and exit occurred.
All ten named declarations passed a fresh source build, a transitive axiom
audit, and standalone kernel replay. Only propext, Classical.choice, and
Quot.sound occur. Existing LeanControls and mathlib artifacts remain trusted
dependencies. This module does not prove the full direct-feedback prefix.

Independent challenge
Another agent reviewed the Taylor bounds, interval rounding, exact flow,
clamp handling, convex energy bound, and whole-hold position bound. It found
no soundness defect in the prototype. This is not an external human review
or a replacement for the missing Lean proof. See challenge.txt.

What would make the paper stronger
1. Prove reusable Lean rules for one held interval. Discharge the exponential
   coefficient bounds and the soundness of the state and position enclosures.
2. Check a short trace first and measure elaboration and kernel replay cost.
   Then check all 25 steps and the complete closed parameter covering.
3. Connect the trace to any actual sampled ODE execution. Prove existence,
   full-state continuity, terminal entry, and the common robust tail.
4. Repeat the fixed region family with checked certificates. Record admitted
   volume, certificate bytes, generation, elaboration, and replay separately.
   Keep enclosure failures distinct from actual counterexamples.
5. Establish external value. Seek independent reuse or comparison with an
   existing verification method. A useful tolerance for brake-phase errors
   or switch-time uncertainty is another candidate, but remains unproved.

Working assessment: B-minus case-study candidate. The comparison now asks
the right question. It does not yet establish a publishable new control
method. More lemmas, a new title, or an animation alone do not change that.

Reproduction from the workspace root
  python3 research/adjacent-controls/direct-comparison/verify_switch.py
  python3 research/adjacent-controls/direct-comparison/prototype.py --hold 1/20 --steps 25
  python3 research/adjacent-controls/direct-comparison/family.py
  python3 research/adjacent-controls/direct-comparison/family-refined.py
The Python runs write their corresponding result files. Elapsed times and
timestamps can change. Fraction bounds and trace hashes should agree.
The .1-period diagnostic has a different terminal time, 1.3. Its preserved
trace is prototype-h010-results.json; it is not the matched-T comparison.

Writing and paper
The revised paper title is "Brake, Switch, Stay Safe", with a technical
subtitle. The workspace AGENTS.md records Mike's preference for writing
inspired by ASD-STE100 at about 80%. This is a style target, not a measured
compliance score. Mathematical precision and exact assumptions take priority.
No external submission, upload, hardware test, or prize claim occurred.
