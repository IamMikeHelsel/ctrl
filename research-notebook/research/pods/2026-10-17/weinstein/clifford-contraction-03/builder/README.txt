Clifford scalar contraction — approved gate 03

The four proof sources submitted for independent review are:
  CliffordModel.lean         Actual Fin 14 quadratic form and Clifford generators.
  ContractionAlgebra.lean    General finite-index identity and sorted-pair bridge.
  CliffordContraction.lean   Weighted tensor and actual Clifford instance.
  CliffordControls.lean      Sectional and non-Bianchi controls in the same algebra.

Run verification from any directory:
  python3 /absolute/path/to/this/folder/verify.py
The script uses this workspace's pinned lean-controls project and local elan.
It builds fresh source copies, audits every exported theorem in these modules,
replays each module with leanchecker, and requires two false-sign checks to fail.
The original definition-audit-02/analyst manifest is checked before and after.
No pre-existing proof source or toolchain pin is changed.

Read conventions.txt for the exact tensor and sign conventions. Read report.txt
and verification.json for the result and completed checks. Theorem counts record
audit coverage only. They are not a progress or scientific-value score.

Build caches are disposable. The sources, scripts, logs, checksums, report and
recorded evidence are the preservation scope. attempts/Probe.lean.txt is an early
API probe, not a submitted proof source. Files ending .lean.txt retain audit and
negative-test inputs; they are not imported by the four proof modules.

This proves one standard real Clifford identity for a declared candidate.
It does not identify the author's preferred GU tensors or prove a field theory.
Independent grader acceptance and notebook storage are separate coordinator work.
