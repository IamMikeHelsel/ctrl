Final-hold settling proof — builder milestone 01

Read report.txt first. The source freezes and fresh verification are separate.
Independent review is not part of this builder package.

Reproduce from the research workspace:
  python3 research/overnight/2026-10-18/controls/builder-01/dev.py
  python3 research/overnight/2026-10-18/controls/builder-01/verify.py

The development helper uses cached local modules to shorten edits. The verifier
copies the complete local source closure into a new temporary directory and
builds it from source, then audits its public theorems and replays selected
modules with leanchecker. It reuses only the pinned Mathlib package cache.
No toolchain or inherited proof source is modified.

Pinned Lean and Mathlib details are recorded in verification.json. The final
artifact manifest includes source, reports, scripts and logs; build caches and
Python bytecode are excluded. Root owns repository storage and remote reporting.

Primary entry points:
  LeanControls.Settling.actual_settling_scaled
  LeanControls.Settling.settling_physical_bounds
  LeanControls.DirectSettling.fixed_reference_then_hold
  LeanControls.DirectSettling.fixed_reference_then_zero_disturbance_hold

The first two are parameterized. The final two compose with the accepted frozen
motion without introducing an independent endpoint-state bound.
