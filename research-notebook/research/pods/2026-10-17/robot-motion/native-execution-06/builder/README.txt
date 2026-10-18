NATIVE-EXECUTION-06 — FIXED FIDELITY REPAIR

Read report.txt and contract.txt first. This package uses native C++ state carry
for each Ruckig replan, then an explicit piecewise-polynomial physical model.
It does not promise bit-identical jerk branching or physical firmware behavior.
The previous05 native-clock audit remains failed. This is a separate frozen gate.

All 144 cases at both resolutions are complete. Native preflight passed before
plant. Independent physical acceptance is pending. There are no task-decision
changes from 05, but some command total-variation values change substantially
because very short native phases change finite jump counts.

Entry files
  contract.txt,clock-edge-cases.txt    Exact execution/clock/stop requirements
  pre-run-input-manifest.json         Inputs before native generation
  pre-run-implementation-manifest.json 94 files before all plant runs
  native_execution.cpp               Primary native retained-history generator
  profile_export.hpp                 In-process native trajectory serializer
  native_replay.cpp                  Separate native replay frontend
  native-build-provenance.json        Source/library/frontend hashes and flags
  native-plans/                      Raw native input/output for all 12 histories
  ruckig-primary-exports.json         All 492 plans, states and binary metadata
  reference-schedules.json           Physical piecewise-polynomial interpretation
  ruckig-primary-validation.json      All 492 local checks
  native-pre-run-gate.json            All 12 whole-history fixed-tolerance checks
  native-checks/                     Saved native replay inputs/outputs
  clock-and-duration-audit.json       Clock offsets, durations and collapsed phase
  raw-fir-reference-equality.json     Entire raw/FIR schedules equal05
  implementation-changes.diff         Changes to inherited primary code
  metrics.csv,metrics.json            All 288 metric rows
  traces/                           Per-case traces and event CSVs
  event-states.json                   Physical state at every event
  decision-comparison-05.json         Full05-to 06 metric and decision changes
  metric-delta-summary.csv            Compact24-group numeric delta table
  jump-sensitive-delta.json           Short-phase/command-jump diagnosis
  comparison-table.csv              24-group final metric table
  isolated-step-latency.json          Reference duration versus actual settling
  refinement.json                    1 ms versus .5 ms checks
  execution-record.json               Preflight, run, completion and log evidence
  preservation.json                  Prior05 and pre-run hash checks
  artifact-sha256.json                Final inventory and freeze timestamp

All data are synthetic. The irregular stream has nonzero dwell-weighted mean;
the random stream is one fixed realization; the deliberate bias case stays
visible. Full input definitions and original bytes are preserved from 05.

Reproduction sequence

Use a new sibling copy. Do not rerun writers inside either frozen builder folder.
The local build expects the verified05 source and static library in its excluded
.cache. Restore that pinned dependency in the copied tree if needed. No install
or source download was performed for 06. The native pin is
99751e6ebc7c963bb80e99fbbe66f2c279d1db57, cloud disabled.

  python3 -B build_native.py
  python3 -B make_references.py
  python3 -B check_native_gate.py
  python3 -B clock_audit.py

Stop if any fixed native check fails. Freeze the reproduction's implementation,
exports and native gate with a new timestamp before plant. Build path/provenance
changes require a new reproduction manifest; do not rewrite or claim equality
with this recorded manifest without checking hashes. The physical runner checks
that manifest and the passing native gate before it executes.

  python3 -B run_comparison.py
  python3 -B audit_results.py
  python3 -B summarize_deltas.py

The last two commands read saved data; they do not run a plant or native replay.
The run contains exactly144 parameter cases at 1 ms and .5 ms. No special source
case was added after results. The independent reviewer has its own oracle and
physical replay driver in ../grader/.

This builder is stopped. The root agent performs notebook sync/check and Git.
