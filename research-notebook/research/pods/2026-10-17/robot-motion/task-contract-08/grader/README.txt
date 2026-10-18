Independent review artifacts — frozen after completion

Start with review-report.txt and grade.json. Proof evidence is in proof-review.json,
logs/, copied build/*.lean sources, and fresh-build-object-hashes.json. Build
objects are excluded after their hashes are saved. The failed reviewer cast
attempt remains in attempts/reviewer-cast-01/. No builder failure was hidden.

The public proof audit covers 689 statements, not all compiler-generated private
declarations. Separate kernel replay checks the listed modules. The builder's
larger declaration count is a different metric and must not be added to this one.

moving_physical_replay.py is separate from the primary simulator. Its outputs
are physical-review.json, moving-review-summary.json and per-event state files.
It replays frozen moving-goal08 polynomial schedules, not a robot or native
firmware. schedule_binding_audit.py independently binds inputs and exported
polynomials. reversal_reference_audit.py uses exact fractions for FIR extrema.
ReviewIntegrationWitnesses.lean includes a Lean proof of the accepted-jerk /
excess-acceleration counterexample. rest_counterexample.py is an analytic check,
not a Lean-certified trajectory.

Reproduce only in a COPY of the working tree so frozen evidence stays unchanged.
Use existing local runtimes. No paid or hosted runner is required.

1. python3 research/pods/2026-10-17/robot-motion/task-contract-08/grader/proof_review.py TaskShape IsolatedHistory TaskContract TaskFixtures ReviewTaskWitnesses ReviewIntegrationWitnesses
2. python3 research/pods/2026-10-17/robot-motion/task-contract-08/grader/negative_controls.py
3. .tools/research-python/bin/python research/pods/2026-10-17/robot-motion/task-contract-08/grader/moving_physical_replay.py c4714051bd9ddf0c44f6e64eef7cf83b35c40494db5be11b10c8ae4cdb171fb3
4. python3 research/pods/2026-10-17/robot-motion/task-contract-08/grader/schedule_binding_audit.py
5. python3 research/pods/2026-10-17/robot-motion/task-contract-08/grader/reversal_reference_audit.py
6. python3 research/pods/2026-10-17/robot-motion/task-contract-08/grader/contract_audit.py
7. python3 research/pods/2026-10-17/robot-motion/task-contract-08/grader/rest_counterexample.py
8. python3 research/pods/2026-10-17/robot-motion/task-contract-08/grader/preservation_review.py

The ordinary system Python does not include mpmath. Physical replay used the
existing .tools/research-python runtime (Python 3.14.0, mpmath 1.3.0, 80 digits).
Lean uses .tools/elan and the lean-controls 4.35.0 / Mathlib pinned environment.
No runtime or dependency was installed or changed for this review.
