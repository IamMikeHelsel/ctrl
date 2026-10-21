"""Adversarial review of the isolated Farkas sketch; no production checker claim."""

import contextlib
import io
import json
import runpy
from fractions import Fraction as F
from pathlib import Path

root = Path(__file__).resolve().parent
with contextlib.redirect_stdout(io.StringIO()):
    producer = runpy.run_path(str(root / "inventor_farkas.py"))
certificate = producer["certificates"][(1, 2, 3)]
wrong_branch = (2, 3, 4)
accepted, total = producer["evaluate"](certificate, F(1, 100))
# The test point belongs to branch234 but contradicts row1, which is not an
# inequality of that branch. The arithmetic checker cannot see the relabeling.
x, y = F(0), F(0)
assert abs(y) <= F(1, 100)
assert abs(x + y) <= F(1, 100)
assert abs(x + 2 * y) <= F(1, 100)
assert accepted
result = {
    "claimed_branch": wrong_branch,
    "borrowed_certificate_branch": [1, 2, 3],
    "arithmetic_only_evaluator_accepts": accepted,
    "combined_inequality": list(map(str, total)),
    "retained_branch_feasible_witness": ["0", "0"],
    "finding": "Sketch has no branch argument; borrowed row1 can wrongly reject valid234 if consumer mislabels it. Static manifest/duplicate assertions are illustrative controls, not a general consumer.",
    "required_repair": "Bind every inequality to claimed original observation membership, model hash, noise bound and complete branch manifest; then bind returned mean to certified Y,eta.",
}
(root / "pm_binding_negative.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    "Confirmed missing branch-to-inequality binding in arithmetic-only sketch; preserved for next block"
)
