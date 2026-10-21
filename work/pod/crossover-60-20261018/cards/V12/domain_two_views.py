"""Exact second SPD metric for the two tilted homographies; no numerical solver."""

import json
from fractions import Fraction as F
from pathlib import Path

p = Path(__file__).parent
r = json.loads((p / "domain_rank.json").read_text())
A = [[F(x) for x in row] for row in r["cases"][1]["A"]]
b = [F(x) for x in r["normalized_b_B11_1"]]
v = list(map(F, [0, -24, 8, 30, 3, -20]))
assert all(sum(x * y for x, y in zip(row, v, strict=True)) == 0 for row in A)
b2 = [x + y / 1000 for x, y in zip(b, v, strict=True)]
assert b2 != b and b2[0] == b[0] == 1
assert all(sum(x * y for x, y in zip(row, b2, strict=True)) == 0 for row in A)
a, c, d, e, f, g = b2
B2 = [[a, c, e], [c, d, f], [e, f, g]]
minors = [a, a * d - c * c, a * d * g + 2 * c * e * f - a * f * f - d * e * e - g * c * c]
assert all(x > 0 for x in minors)
false_prior = [x - y / 144 for x, y in zip(b, v, strict=True)]
assert false_prior[0] == 1 and false_prior[1] == 0 and false_prior != b
assert all(sum(x * y for x, y in zip(row, false_prior, strict=True)) == 0 for row in A)
a, c, d, e, f, g = false_prior
false_minors = [a, a * d - c * c, a * d * g + 2 * c * e * f - a * f * f - d * e * e - g * c * c]
assert all(x > 0 for x in false_minors)
result = {
    "null_direction": v,
    "false_zero_skew_prior_metric": false_prior,
    "false_zero_skew_prior_minors": false_minors,
    "normalized_metric_original": b,
    "normalized_metric_alternative": b2,
    "alternative_matrix": B2,
    "leading_principal_minors": minors,
    "scope": "Two tilted views retain distinct SPD intrinsic metrics. Existence of normalized positive upper-triangular K from SPD and pose reconstruction is a hand-derived bridge, not kernel-checked here.",
}
(p / "domain_two_views.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print("Exact second SPD solution; principal minors:", list(map(str, minors)))
