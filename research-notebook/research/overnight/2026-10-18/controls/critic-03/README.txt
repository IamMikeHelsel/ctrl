Independent varying-input scout review 03

Decision and scope: review.txt.
Recommended bounded certificate gate: next-gate.txt.

Evidence
- numeric-review.json: exact input checks, all saved vertex score replays,
  independent physical-coordinate DOP853 and adjoint, budget checks, controls.
- physical-series.json: independent 80-digit scalar physical ODE replay.
- independent-physical-traces.npz: nine physical-state traces for frozen input.
- review_numeric.py and physical_series.py: reviewer source.
- runtime.json: numerical library versions.
- review-attempt-01/ and review-attempt-02/: preserved reviewer harness failures.
- artifact-sha256.json: frozen reviewer outputs; compiled cache excluded.

The review did not run an optimizer or build the proposed certificate.
Compile the frozen builder scout_kernel.cpp to this folder's .cache/review_kernel.dylib
to reproduce fixed-score replay. Use the existing default Python for review_numeric.py
and .tools/research-python/bin/python for physical_series.py. Do not overwrite
frozen outputs; replay into a copy. The parent owns repository preservation.
