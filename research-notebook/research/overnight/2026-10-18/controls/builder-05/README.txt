FIR RETURN TO QUADRATIC HOLD — BUILDER 05

This folder owns one proof-composition candidate. Read CLAIMS.txt and the exact
FIRHold.lean theorem statement. FIRHoldWitness.lean gives explicit moving physical
trajectories and false-claim witnesses. Independent acceptance is pending.

Inherited proof sources in inherited/ were copied byte-for-byte after checking
both accepted manifests. setup.py and inherited-check.json record provenance.
New proof sources import those copies. No parent proof or toolchain was edited.

Development: python3 research/overnight/2026-10-18/controls/builder-05/dev.py FIRHoldWitness
Final verification: python3 research/overnight/2026-10-18/controls/builder-05/verify.py
These commands write into this folder. After freezing, run them only in a
fresh review copy at the same folder depth; preserve the frozen original.
The verifier uses the existing pinned Lean 4.35.0 and Mathlib checkout. It builds
the full local dependency closure into a new temporary folder; only the pinned
Mathlib/package cache is reused. It audits all imported local declarations,
including private declarations, and separately runs leanchecker on key modules.
Six negative clients must fail on their intended exact false assertions.

Failures are retained in numbered logs and source copies. Final artifact hashes
are recorded only after the batch stops. The builder does not accept its own work.
Repository sync, commit, push, paper integration and independent review are root
responsibilities. This folder makes no numerical performance or hardware claim.
