FROZEN COMMON-PREFIX COMPARISON

Read report.txt and protocol.txt first. Builder evidence awaits independent
review. All work here belongs to one bounded numerical milestone.

Replay order, from this working research root:
1. Use /Library/Frameworks/Python.framework/Versions/3.14/bin/python3.
2. Run builder-03/build_native.py. This checks the existing pinned native source
   and library, then builds two small local frontends into .cache/.
3. Run builder-03/prepare_comparison.py. It verifies pre-run-freeze.json and
   creates the exact FIR prefix, native plans, query gate and schedule freeze.
4. Run builder-03/run_experiment.py, then summarize.py and audit_results.py.
5. Optional plot_comparison.py uses the separate recorded figure runtime.

Use a new replay folder to preserve this frozen bundle. Scripts locate inputs
relative to their own file. The inherited build_native.py source path resolves
the pinned latency-noise-05 library in this workspace. Its provenance and
source hashes are in native-build-provenance.json. Build caches are excluded
from repository storage. Root owns repository sync, commits and PR26.

Authoritative gates:
- pre-run-freeze.json: inputs/protocol/runtime/implementation before execution.
- reference-freeze.json: exported plans, native checks, schedules before plant.
- data-sha256.json: all metrics and raw physical traces.
- artifact-sha256.json: final bundle except caches and the manifest itself.

No new Lean theorem, hardware result, novelty result or external submission.
