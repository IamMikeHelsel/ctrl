ROUNDED HANDOFF 07 — BUILDER ARTIFACT

Main proof: RoundedHandoff.lean.
The finite_replans_with_jumps_scaled theorem obtains segment tracking from the
actual plant ODE and propagates a nonzero reference-jump reserve at each handoff.
finite_cubic_replans specializes it to the proved cubic reference family.
HandoffWitnesses.lean proves concrete positive cases and necessary assumptions.
theorem-guide.txt explains the mathematical contract and its limits.

NativeCoverage.lean proves that a checked rational piece chain covers every
absolute real time in its closed horizon. NativeGlobal.lean composes that result
with the checked physical tracking theorem. It does not assume tracking anew.
The sibling bindings/ directory contains the separately owned NativeData,
NativeBridge and NativeInstances sources. Their source freeze is recorded in
coverage-source-freeze.json and global-source-freeze.json.

Verification uses the existing pinned Lean and Mathlib environment. verify.py
copies and compiles the full 38-module local closure, audits every local
declaration for standard axioms and unsafe code, replays three modules through
leanchecker, and tests four false variants. integration_verify.py then copies
and compiles five integration modules against that fresh closure, audits all
43 modules, replays the five new modules and tests a false clock-gap acceptance.
The recorded JSON files include commands, source hashes, log hashes and times.
Build caches are excluded from preservation.

To reproduce without modifying this freeze, copy this directory to a new sibling
directory, excluding .cache and __pycache__. Keep the sibling bindings directory
at the same level. Run python3 verify.py from the copy, then run
python3 integration_verify.py. Each script refuses to reuse its build directory.
The development helper and logs are not acceptance evidence.

The first verification attempt stopped because its comment scanner processed
line comments before block comments. The word unsafe in an existing doc comment
was misread as code. No Lean source changed. The complete failed attempt is kept
under attempt-1-*; the corrected verifier rebuilt a new empty local closure.

The result is conditional on the stated actual plant trajectories, response-rate
and disturbance bounds, initial error, and exact physical-state handoffs. It is
not a physical experiment, a proof of native floating-point execution, a new
planner, or a true-goal/hold-band certificate. Prior numerical failures remain
unchanged. Notebook sync, commit and remote preservation are parent-owned work.
