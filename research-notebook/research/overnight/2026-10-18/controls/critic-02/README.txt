Independent constant-bias controls review 02

Read review.txt for the decision and scope. Read next-test.txt for the single
recommended follow-up. No follow-up experiment was run during this review.

Evidence
- independent_verify.py: independent import closure, hash checks, fresh builds,
  public-axiom audit, proof replay and rejected false controls.
- verification.json: fresh frozen-source results and the preserved first
  reviewer-fixture failure.
- final-verification.json: repaired reviewer fixture, its kernel/axiom checks,
  five rejected false controls and unchanged-source checks.
- ReviewWitnesses.lean: full nonzero-bias composition, retained-state and
  counterexample checks added by the reviewer.
- negative/: five false statements that must fail for mathematical reasons.
- logs/: complete fresh-build, audit, kernel and false-control logs.
- review-attempt-01/: retained reviewer development failure; no frozen change.
- artifact-sha256.json: frozen review files. Build caches are excluded.

Reproduction uses the existing pinned Lean/Mathlib workspace. In a fresh copy of
this review folder, create empty build/ and logs/ directories, then run
python3 independent_verify.py. The verifier refuses to reuse local .olean files.
It does reuse the pinned Mathlib cache. No builder Python helper is imported.

The parent owns repository synchronization, commits and shared manuscript edits.
No hardware, publication novelty, or submission approval follows from this review.
