Independent review of builder-03's actual real matrix-adjoint bridge.

Run from any working directory with this workspace and its pinned dependencies:
  python3 /absolute/path/to/critic-03/review_lean.py
  python3 /absolute/path/to/critic-03/review_exact.py

The Lean replay requires an empty critic-03/cache directory. Preserve earlier
runs rather than overwriting a frozen review. Every local module is compiled
from builder sources whose manifest is pinned in review_lean.py. Only pinned
third-party dependencies and compiler products are reused. The project build
cache is excluded. Do not change the Lean or Mathlib pins to fit another project.

REPORT.txt and decision.json give the decision. lean-review.json records fresh
compilation, all local declaration axioms, six false controls, and separate
kernel replay. exact-review.json is an independent exact finite calculation.
SCOPE.txt gives the mathematical boundary. NEXT-GATE.txt gives one follow-up.
SHA256SUMS freezes this review, excluding transient cache products and itself.

The first reviewer harness preflight rejected the toolchain's own library path.
It stopped before any compilation. The original script and diagnosis are saved.
The corrected harness admits that exact pinned path, still excluding all local
project build products. This was a review harness issue, not a theorem failure.

Root owns repository synchronization, commits, pushes and manuscript changes.
This worker wrote only critic-03. Nothing was submitted or sent externally.
