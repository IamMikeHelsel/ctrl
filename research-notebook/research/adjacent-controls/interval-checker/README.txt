Reusable interval checker and direct-feedback pilot

Run from the workspace root:
  python3 research/adjacent-controls/interval-checker/verify.py

Requires the pinned lean-controls project and local .tools/elan installation,
or RECOVERY_LAKE pointing to a compatible lake executable. The local name is
retained from the companion recovery verifier. No network install is performed.

verify.py regenerates coefficient assertions in check mode, rebuilds the twelve
new modules and the existing TerminalBase dependency in a temporary directory,
audits every public named theorem, and replays every module with leanchecker.
A false terminal-energy claim must be rejected. Pinned base and mathlib artifacts
remain dependencies; this does not bootstrap the Lean compiler.
See verification.json for measured results and verification-logs for details.
The latest full replay passed for 64 new named theorems plus 2 declarations in
TerminalBase. The false terminal-energy claim was rejected. Counts describe
audit coverage, not distinct research contributions.

Module chain:
  IntervalChecker: rational intervals, held step, finite endpoint composition.
  CoefficientBounds -> CoefficientCells: exact exponential coefficient bounds.
  TraceExecution: endpoints of actual fixed-rate continuous executions.
  IntervalPilot -> IntervalPilotActual: accepted 25-step pilot and coefficient link.
  PilotSafety: terminal V<=12, actual-execution entry and existence.
  BetweenSample -> PilotPath: position containment throughout each closed hold.
  FiniteHandoff -> PilotContinuation: prefix-only restrictions and robust tail.
  GeneralHandoff: any safe continuous prefix with terminal V<=12 can be joined
    to the fixed-rate sampled controller. Prefix dynamics are a separate duty.

Pilot only:
  x=[0.99,0.995], v=[0.49,0.495], a=[-0.01,-0.005], r=[0.9,0.9125].
  First 25 holds are 0.05 with zero errors; terminal time is 1.25.
  PilotContinuation proves actual all-time position safety for this one cell.
  Holds after the prefix may vary up to 0.2, with combined held command error
  |e_n|+|d_n|<=1/90. A positive global lower dwell bound is required.
  The same unknown r is fixed for the entire execution.
  The full original initial-box/rate covering remains unchecked in Lean.
  No hardware validity, improved control performance, standstill deadline,
  maintained stop, or ISO 13849 Performance Level is established.

The pilot generator supplies proposed boxes. Acceptance comes from Lean, not
from trusting the generator. generate_pilot.py overwrites its two generated files;
do not run it while checking frozen source hashes.

Roadmap: downstream-roadmap.txt.
Independent challenge: final-challenge.txt and application-and-checker-review.txt.
Latest composition review: composition-and-novelty-review.txt.
Research direction: ../adjacency-review/index.html. The broader literature
screen supersedes the earlier proposal to treat more certified boxes as the
main publication gate. The new variable-response envelope remains a proposal.
Paper diagrams: ../../../publication/recovery-manuscript/images/.
