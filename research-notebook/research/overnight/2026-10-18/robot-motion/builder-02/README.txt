ACTUAL POSITION COMPOSITION AND A NEW FIXED COMPARISON

Read report.txt, protocol.txt and runtime-replay-02/comparison-table.csv first.
The canonical numerical run is runtime-replay-02/. Root-level numerical
outputs preserve the earlier run with a different numerical runtime.

Proof
  PhysicalArrival.lean: delayed_return_physical_position uses the full retained
  delayedReturn history and actual scalar plant from time zero. It proves a
  0.2 mm position tube, at least 1 mm actual progress by 0.5 s, and position
  arrival from 1.42 s through 2.50 s. Rate may vary within [80,120] /s and
  disturbance magnitude may vary up to 0.01 m/s^2, subject to the stated
  trajectory/controller assumptions. The initial transformed error cube is
  at time zero. zero_initial_cube discharges that premise for actual state 0.
  There is no reset at either revision time. Actual speed, acceleration and
  physical rest are not conclusions.

  verify02.py is the final verifier. Use source-freeze-02.json and
  verification-02.json. It builds the full local closure in a fresh directory,
  audits standard axioms and unsafe declarations, runs separate kernel replays,
  rejects four false claims and rechecks source/pin hashes.

  The first verifier's lexical scan rejected the inherited ordinary function
  named admit. The old verifier, source freeze, failed run and partial logs
  are preserved. The correction removes that false-positive token rule.
  The environment audit still rejects sorryAx and every nonstandard axiom.
  PhysicalArrival.lean did not change between those verifier runs.

Numerical batch
  pre-run-input-manifest.json froze the protocol and packet data before any
  new reference or physical result. pre-run-implementation-manifest.json
  froze implementation, native checks, reference schedules and binaries before
  physical runs. data-sha256.json froze all raw traces and metrics immediately
  after the batch. No parameter or pass criterion was changed.

  There are 96 traces: two deadline tasks, four methods, three rates, two
  disturbances and two output grids. All event-side states are preserved.
  The native fast and minimum_duration 0.8 frontends, state carry and plans
  match moving-goal-08. Separate native replay passes before integration.
  The physical integration helper run_comparison.py is byte-identical to08.

  The first delivered packet contains no revision deadline. Only the second
  packet supplies it. The new method tries [0.52,0.62] s. It selects 0.62 s
  for the 1.70 s deadline and rejects the revision for the 1.30 s deadline.
  A rejected revision remains a task failure; its old reference continues.
  actual_selected_execution_s is null for rejection. execution_s in the
  admission row is then only the requested-time audit probe.

  prepare.py, build_native.py and check_native_gate.py prepare the references.
  run_batch.py executes only the frozen batch; run_comparison.py is imported
  for its unchanged propagation function. Do not invoke its old standalone
  main. summarize.py and audit_batch.py read saved data without physical runs.
  make_references.py also retains an unused old main; do not invoke it.

Reproduction
  Use a NEW sibling directory, excluding .cache, generated outputs and build
  objects. Preserve the pinned Lean/mathlib and local pinned Ruckig library.
  No install or model change is needed. Regenerate and freeze a new native
  implementation manifest because binary paths/provenance may change.
  Do not overwrite this frozen run or its evidence. Cached native binaries
  are excluded from Git; hashes and complete sources are preserved.

  Final artifact hashes exclude .cache and __pycache__. This directory is
  owned by the numerical/proof builder. Independent review belongs elsewhere.

Runtime correction

  The first run used the installed Franka Python 3.12 environment with NumPy
  2.5.4 and SciPy 1.18.1. The recorded06 environment was system Python 3.14.0,
  NumPy 2.3.4 and SciPy 1.16.2. The mismatch was found before handoff. The
  first run was preserved. runtime-replay-02/ repeats the same frozen inputs
  and implementation in the recorded environment, with a new runtime freeze
  before its physical run. It is the canonical numerical result.

  Every task decision agrees across runtimes. All 362724 saved state rows
  were compared. Maximum position difference is 1.39e-17 m. See
  runtime-comparison.json for all differences. This correction is not an
  independent physical replay. Both runs and all failure cases are retained.
