LATENCY-NOISE-05 BUILDER — FROZEN WITH A FAILED NATIVE-CLOCK AUDIT

Read report.txt first. All 144 canonical parameter cases are present at both
sampling resolutions. This gate is not accepted. A later native-clock audit
failed the fixed acceleration tolerance; seven replay pairs remain unrun.

Entry files
  contract.txt                         Fixed scope and tolerances
  pre-run-input-manifest.json           Nine files frozen before implementation
  pre-run-implementation-manifest.json  Implementation/references before plants
  packets.json, observation-times.json  All six explicit synthetic streams
  input-mean-audit.json                 Arithmetic and dwell-weighted means
  metrics.csv / metrics.json           All 288 metric rows
  comparison-table.csv                 24 method/stream summaries
  traces/                              Per-case compressed traces and event CSVs
  event-states.json                     Physical state at every event
  isolated-step-latency.json            Actual duration and sampled settling
  native-duration-audit.json            All native planned durations
  native-clock-failure.json             Failed witness and clock comparison
  failed-native-clock-plan.json         Native-input profile around the witness
  native/                              Five saved native replay inputs/outputs
  native-replay-partial-audit.json       Four pass, one fail, seven not run
  refinement.json                      1 ms versus .5 ms, same builder
  original-case-regression.json         72 unchanged old metric rows
  fir-ablation-equality.json            Guarded/unguarded input-history identity
  admission-transcripts.json            Exact rational admission decisions
  fir-exact-enclosures.json             Exact finite reference bounds
  ruckig-primary-exports.json           Positive/zero phases and binary metadata
  ruckig-primary-validation.json        Same-input native reconstruction checks
  ruckig-provenance.json                Pin, source/build hashes, flags and license
  verified-code-changes.diff            Changes from comparison-04
  run-record.json / audit-failure.txt   Completion record and preserved failure
  preservation.json                    Prior and pre-run manifest checks
  artifact-sha256.json                  Final file inventory and hashes

The .2 s FIR width is exactly five periods of the original hold_jitter input.
The irregular stream has zero arithmetic mean but mean -1/2600 m when weighted
by dwell time. The seeded sample mean is -10.95 micrometres. The explicit bias
stream has mean +.4 mm. No input was altered after the pre-run freezes.

Reproduction sequence (not rerun after the stop)

Do not overwrite this frozen folder. Work in a new sibling copy and preserve the
relative location of comparison-04 and lead-01, which are read-only dependencies.
Use the recorded Python/Numpy/SciPy runtime and pinned local Ruckig build.

  python3 -B build_ruckig.py
  python3 -B ruckig_checks.py
  python3 -B duration_smoke.py
  python3 -B make_references.py
  python3 -B run_comparison.py
  python3 -B audit_latency_noise.py

The physical runner verifies pre-run hashes. A fresh rebuilt binary or changed
provenance can differ across environments; record that as a new reproduction
manifest before running, without changing the frozen inputs or claimed equality.
The extra audit is expected to stop at the saved native-clock acceleration
comparison on the recorded platform. No cross-platform bit equality is claimed.

The failed case can be diagnosed without another plant run:
  python3 -B diagnose_failed_clock.py

Existing saved results can be summarized without native execution or integration:
  python3 -B summarize_stopped_gate.py

That summary command creates summary files; run it only in the new copy. The
original physical command's output was not redirected to a persistent file.
run-record.json labels its terminal completion data as a transcription. The
empty audit-log.txt is preserved; audit-failure.txt records the observed stderr
assertion without pretending to be a full raw traceback.

The canonical rational clock uses exact commit times plus exported native
cumulative boundaries. It does not sum exact binary phase durations. All native
t/t_sum, endpoints and binary ratios are retained. Native replay instead uses
native absolute-double subtraction across commits. Those are distinct execution
representations. The failed strict comparison is visible in both report and data.

No claim of independent acceptance, formal plant verification or robot hardware
success is made. The root agent performs notebook sync/check and Git preservation.
