Think Often, Switch Smoothly

Read report.txt for the result, prior work and limits.
SmoothReplan.lean contains 24 public theorem statements.
verification.json records the checked source and toolchain hashes.
examples.json gives three exact-rational illustration cases.

Reproduce from the workspace root:

  python3 research/adjacent-controls/vla-smooth-replanning/verify.py

The verifier creates a temporary directory, builds the new source, audits all
public theorem closures, replays the module with leanchecker, and confirms that
an incorrectly tightened jerk limit cannot be admitted. It reuses the workspace's
pinned LeanControls/mathlib dependencies. It does not install software.

This proves conditional properties of scalar commands and mathematical splices.
It does not run a VLA, Ruckig, robot, dynamics simulator or hardware experiment.
The exact-rational examples are not measured outcomes.

Novelty has not been established. This is a formal certificate prototype using
known trajectory mathematics. The report identifies a next comparison and the
remaining connection to uncertain physical stopping and task progress.
