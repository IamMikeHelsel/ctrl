Independent GU review 01

Read REPORT.txt for the verdict and boundaries. Read ERRATA.txt before using the
analyst's source questions. QUESTIONS-FOR-AUTHOR.txt is the corrected unsent list.
NEXT-GATE.txt is a bounded continuation recommendation, not an accepted result.

Reproduce from the research root:
  python3 research/overnight/2026-10-18/geometric-unity/critic-01/review_lean.py
  .tools/franka-sim-python/bin/python research/overnight/2026-10-18/geometric-unity/critic-01/review_adjoint.py

The first command uses the existing pinned Lean and Mathlib installation. The
second uses the existing local Python/Numpy runtime. No model service is called.
cache/ contains disposable local build and page-render files. SHA256SUMS excludes
cache/ and itself. Frozen analyst sources are only read.
