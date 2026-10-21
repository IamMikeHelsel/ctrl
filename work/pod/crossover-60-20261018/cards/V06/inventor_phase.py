"""Exact weighted-frustration boundary: same holonomy, unique optimum."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
a, b, c = F(8), F(3), F(4)
weights = [a * b, b * c, a * c]
laplacian = [[a * (b + c), a * b, a * c], [a * b, b * (a + c), b * c], [a * c, b * c, c * (a + b)]]
dual = [0, 2 * b * c, 2 * b * c]
slack = [[laplacian[i][j] - (dual[i] if i == j else 0) for j in range(3)] for i in range(3)]
vectors = [[7, 3, 4], [0, 1, -1]]
coefficients = [F(8, 7), F(12, 7)]
factorized = [
    [sum(d * v[i] * v[j] for d, v in zip(coefficients, vectors, strict=True)) for j in range(3)]
    for i in range(3)
]
assert slack == factorized
assert all(d > 0 for d in coefficients)
kernel = [1, -1, -1]
assert all(sum(row[j] * kernel[j] for j in range(3)) == 0 for row in slack)
assert slack[0][0] * slack[1][1] - slack[0][1] ** 2 == 96
# The two nonzero linear forms force R1=R2 and 7R0+3R1+4R2=0.
# Thus R1=R2=-R0; gauge R0=I removes the last freedom, so unique.
lower = 2 * sum(dual)
assert lower == 96 == 8 * b * c
sum_amplitudes = a + b + c
constant = 2 * sum_amplitudes**2 - 4 * (a * a + b * b + c * c)
assert constant == 94 and constant + 2 * (a - b - c) ** 2 == 96

result = {
    "weights_edges01_12_02": weights,
    "all_measurements": "minus identity in SO(2)",
    "candidate": "R0=I,R1=R2=-I",
    "dual_lambda": dual,
    "slack": slack,
    "positive_SOS_coefficients": coefficients,
    "SOS_vectors": vectors,
    "slack_rank2_minor": 96,
    "kernel": kernel,
    "global_optimum": lower,
    "uniqueness": "positive SOS weights imply R1=R2 and7R0+3R1+4R2=0; fixedR0I gives unique",
    "old_polygon_closure_lower_bound": constant,
    "old_lower_bound_not_attained": "8>3+4, triangle inequality prohibits weighted closure",
    "corrigendum_KKT_negative": {
        "sum_constraint": 2,
        "interior_stationary": [1, 1],
        "interior_sumsquares": 2,
        "boundary_candidate": [2, 0],
        "boundary_sumsquares": 4,
    },
}
boundary_slack = [[49, 21, 28], [21, 9, 12], [28, 12, 16]]
assert boundary_slack[0][0] * boundary_slack[1][1] - boundary_slack[0][1] ** 2 == 0
assert 2 * 14**2 - 4 * (7**2 + 3**2 + 4**2) == 96
assert 7 + 3 * (-1) + 4 * (-1) == 0
result["boundary_case"] = {
    "amplitudes": [7, 3, 4],
    "weights01_12_02": [21, 12, 28],
    "slack": boundary_slack,
    "scalar_slack_rank": 1,
    "optimum": 96,
    "gauge_fixed_unique": True,
    "proof": "zeroSOS gives7+3cos(theta1)+4cos(theta2)=0; eachcos>=-1 forcesboth=-1",
    "lesson": "extra slack nullity doesnot itself demonstrate multiple feasible globalminima",
}
(HERE / "inventor_phase.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(json.dumps(result, default=str, indent=2))
