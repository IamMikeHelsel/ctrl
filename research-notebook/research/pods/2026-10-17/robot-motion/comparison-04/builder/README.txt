Comparison-04 empirical builder

Start with report.txt. All numerical evidence is from synthetic scalar streams.
The fixed parameter set has 72 cases, each evaluated at 1 ms and .5 ms. Independent
high-precision physical review is pending. No new Lean proof is in this folder.

Reproduce in this directory with the existing Python, NumPy, SciPy, CMake and Clang:
  python3 -B build_ruckig.py
  python3 -B ruckig_checks.py
  python3 -B make_references.py
  python3 -B run_comparison.py
  python3 -B audit_results.py

build_ruckig.py downloads only the pinned public source archive. It verifies the
five preflight source hashes, disables cloud support and builds local C++ tools.
Sources/builds/binaries live under .cache and are excluded from the artifact
manifest. ruckig-provenance.json records their hashes and build commands.

metrics.csv / metrics.json: all signed endpoint and smoothness results.
traces/: one compressed CSV and one event CSV per case and resolution.
reference-schedules.json: executed polynomial pieces with exact clock strings.
ruckig-primary-exports.json: all 49 original plans, including unexecuted future
phases, zero-duration metadata, native cumulative clocks, and native query states.
ruckig-smoke-exports.json: the four mandatory source/export smoke fixtures.
hold-jitter-diagnostic.json: worst hold excursion, native commit states, local
phase history and timing-disagreement audit.
native-hold-replay-input.txt / native-hold-replay.json: native retained-state
Ruckig replay. To rerun directly: .cache/native_replay < native-hold-replay-input.txt
refinement.json: 1 ms versus .5 ms comparisons, including event-state changes.
scheduler-audit.json: accepted/discarded packet age, final target age and admission
transcripts. Packet age means time minus that packet's observation timestamp.
event-states.json: primary numerical event states for comparison only. An
independent reviewer must not reuse these as integration starting states.
frozen-*.json: byte-for-byte lead input fixtures and exact reference evidence.
retained-negative-cases.json: rejection, deadline failure and coalescing semantics.
input-preservation.json: all 28 lead/preflight manifest files verified unchanged.
runtime.json: Python/NumPy/SciPy and platform versions.
gate-contract.txt: fixed pre-execution task and tolerances.
time-convention.txt: precise numerical time interpretation and recorded limits.
reproduction.json: same-code byte-for-byte rerun of all generated evidence.

Proof sources, literature and the original contract remain in lead-01 and
ultra-preflight-02. Root owns notebook synchronization, preservation and Git.
