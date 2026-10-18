KERNEL-CHECKED CERTIFICATE ACCEPTANCE PERFORMANCE PROBE
17 October 2026

RESULT
The useful change is small: keep the original step/coordinate case split,
but replace its final norm_num expansion with decide +kernel.

  intro n hn
  interval_cases n <;> intro i <;> fin_cases i <;> decide +kernel

No native_decide, sorry, or new axiom was introduced into an accepted proof.
Existing IntervalPilot.lean, IntervalChecker.lean, pilot-data.json, and
coefficient-data.json were not edited; their hashes remain unchanged.

MEASUREMENTS
Fresh local compilation and separate leanchecker replay, sequential runs:
                                          compile    kernel     combined
  Original norm_num proof, renamed copy     31.671s     9.394s     41.065s
  One forall Fin25 decision                 7.801s    17.979s     25.780s
  75 coordinate decisions, same splits       3.645s     7.832s     11.477s
  Four distinct cells, coordinate decisions  6.440s    11.755s     18.195s

The single-cell split version is about 8.7 times faster to compile and
3.6 times faster for compilation plus kernel replay than the fresh baseline.
The four-cell batch checks 100 transitions, or 300 coordinate inclusions.
These are local wall-clock measurements on the present host, not repeated
statistical benchmarks or controller execution times.

EXPECTED WORKLOAD, NOT MEASURED WHOLE-COVER PERFORMANCE
Repeating the measured four-cell batch cost across 1024 cells would take
about 77.6 minutes sequentially (256 batches x 18.195s). The measured baseline
repeated per cell would take about 11.7 hours. This is an extrapolation only.
Other rate cells, storage, terminal/path acceptance, full-box coverage,
proof composition, scheduling, and memory can change the cost. No full 1024-cell
certificate was generated, checked, or claimed in this probe.

SAME DATA AND SAME STATEMENT
KernelSplit.lean copies the exact original coefficient definition and all
26 saved boxes, changing only the namespace and final arithmetic tactic.
StatementCheck.lean proves by reflexivity that its coefficient and box
definitions equal the original definitions. It then uses the new proof to
inhabit the original checked_steps and endpoints statements unchanged.
StatementCheck compiled in 3.253s and separately replayed in 8.501s.

BatchFour.lean uses coefficient-data rate cell 0 and four adjacent acceleration
cells covering [-.01,.01], each with the original first x and v subcells:
  x in [.99,.995], v in [.49,.495].
Its first data trace was checked to equal pilot-data.json exactly. The other
three traces use the same rational operations and final outward dyadic rounding
as generate_pilot.py. The full rational data is in batch-four-data.json.
Its endpoint theorem retains explicit CoeffMem and initial BoxMem hypotheses.
It is not a proof of the complete initial box, terminal energy, intersample
travel, or an all-time controller theorem.

TRUST AND FAILURE EVIDENCE
Five accepted modules (Baseline, KernelFin, KernelSplit, StatementCheck,
BatchFour) passed leanchecker individually. Their 13 printed theorem closures
use only propext, Classical.choice, and Quot.sound. No unexpected axiom is
accepted. This run reuses already-built checker and pinned LeanControls/mathlib
dependencies; it is not a fresh replay of every imported dependency.

Plain decide over Fin25 failed because elaborator reduction became stuck.
DecideFin.lean and its compile log are preserved. Lean prints sorryAx for the
failed elaboration's incomplete declarations; that run exited 1 and was not
kernel replayed or accepted. Do not count its declarations as proved.

FILES AND REPRODUCTION
benchmark.json records times, toolchain, source hashes, log hashes, exit codes,
and each accepted axiom audit. Module compile/kernel logs are adjacent.
Run from the workspace root, with the existing checker dependencies built:

  .tools/research-python/bin/python \
    research/adjacent-controls/interval-checker/performance-probe/benchmark.py \
    KernelFin KernelSplit DecideFin Baseline StatementCheck BatchFour

The runner rebuilds each requested probe module, times its individual kernel
replay, and appends a run to benchmark.json. It currently overwrites that
module's prior log filenames; copy the probe directory first if preserving
the initial timing logs is required. It does not modify the original checker.

No further proof expansion or full-cover run was started. This is a verification
cost improvement, not a new control-theory result or evidence of application
value. The parent task is evaluating the mathematical and engineering scope.
