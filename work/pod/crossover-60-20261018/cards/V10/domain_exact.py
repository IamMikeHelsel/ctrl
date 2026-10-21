"""Independent rational residual and norm-semantics fixtures; no optimization solver."""

import json
from fractions import Fraction as F
from pathlib import Path

CARD = Path(__file__).resolve().parent


def residuals(point):
    x, y, z = map(F, point)
    assert z > 0
    return [(x / z, y / z), ((x - 1) / z + 1, y / z - F(1, 2))]


def evaluate(point):
    values = residuals(point)
    return {
        "point": [str(F(x)) for x in point],
        "residuals": [[str(x) for x in r] for r in values],
        "squared_euclidean_max": str(max(sum(x * x for x in r) for r in values)),
        "coordinate_max": str(max(abs(x) for r in values for x in r)),
    }


optimum = evaluate([0, F(1, 4), 1])
wrong_norm = evaluate([F(1, 10), F(1, 4), 1])
assert F(optimum["squared_euclidean_max"]) == F(1, 16)
assert F(wrong_norm["coordinate_max"]) == F(1, 4)
assert F(wrong_norm["squared_euclidean_max"]) == F(29, 400) > F(1, 16)
report = {
    "camera1": "[I|0]",
    "camera2": "[I|(-1,0,0)]",
    "observations": [["0", "0"], ["-1", "1/2"]],
    "optimum": optimum,
    "coordinate_norm_mutation": wrong_norm,
    "infeasible_gamma_1_5_certificate": "y≤z/5 and z/2−y≤z/5 imply z/2≤2z/5, contradicting z>0",
    "scope": "Exact finite positive-depth Euclidean image-plane minimax triangulation; no angular-error or unknown-rotation claim.",
}
(CARD / "domain_exact.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
