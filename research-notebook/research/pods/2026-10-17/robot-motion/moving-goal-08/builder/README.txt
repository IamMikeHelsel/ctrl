MOVING GOAL 08

Start with report.txt, protocol.txt and comparison-table.csv.
packets.json gives all exact inputs. No actual robot or Franka model was used.

Freeze/evidence chain:
  pre-run-input-manifest.json     Four cases before any reference/plant results
  pre-run-implementation-manifest.json  Passed native gate, before physical run
  data-sha256.json                Immutable raw batch before independent review
  artifact-sha256.json            Final builder inventory when present

Entry points:
  prepare.py                     Shared authoritative proposals; local FIR guard
                                 and native execution schedules; reference extrema
  build_native.py                Unchanged06 frontend build against pinned local05
                                 Ruckig cache; no install, network or cloud calls
  native_execution.cpp           Native state carry at binary execution times
  native_replay.cpp              Separate native replay frontend
  check_native_gate.py           Fixed reconstruction tolerance and boundary checks
  run_batch.py                   Exactly72cases, two grids; extra task scoring
  run_comparison.py              Byte-identical06 physical integration function
  summarize.py                   Saved-data summaries/refinement/preservation
  audit_causality.py             Saved proposals and committed-prefix audit

Data:
  reference-schedules.json        All12 reference schedules
  ruckig-primary-exports.json     All16 native plans, including duplicate A/B
  reference-extrema.json          Critical-point V/A/J and exact FIR A/J peaks
  admission-transcripts.json      Every proposal, rejection, retained event list
  native-pre-run-gate.json        Eight passing native histories
  metrics.csv/json               All144 result rows
  traces/                       144 compressed traces and144 event/jump CSVs
  task-state-diagnostics.json     Actual states at issue/ready/requested execution
  A-B-physical-identity.json      36 byte-identical deadline-contrast trace pairs
  refinement.json                Fixed-grid deltas; no changed task decisions
  preservation.json              Full earlier05/06 builder hash verification

Reproduction must use a NEW sibling builder copy under robot-motion/. Do not run
writers in frozen folders. Preserve source/input files; exclude.cache, traces and
generated outputs. Use the already provisioned Python numpy/scipy environment
and pinned05 local static library/source cache documented by build_native.py.
Do not install or substitute versions. Run build_native.py, prepare.py and
check_native_gate.py first. Stop on any failed native gate. Freeze a NEW local
implementation manifest over that copy's files before run_batch.py; use the
same schema as pre-run-implementation-manifest.json. Build paths/provenance can
change hashes, so never pretend the original implementation manifest still binds
new build outputs. After the batch, freeze a new data-sha256.json before running
summarize.py and audit_causality.py. No new parameter/grid choice is allowed in
a reproduction. Original raw data are already sufficient for a read-only audit.

The code copied from06 includes unused old standalone mains. Only the entry
sequence above is the08 batch. Do not invoke make_references.py or
run_comparison.py as standalone old-case runners; prepare.py and run_batch.py
use their unchanged helper functions.

Independent review belongs to the critic's separate folder. Builder scope is
numerical evidence and exact rational reference calculations, not a new Lean
proof, a native firmware proof or a hardware safety/task claim.
