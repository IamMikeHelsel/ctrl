"""Exact forcing-channel moment checks; no identification with tracking error."""

import json
from fractions import Fraction as F
from pathlib import Path

J, h, sigma = F(10), F(1, 50), F(1)
signs = [1, -1, -1, 1]
rates = [8 * sigma, 12 * sigma, 12 * sigma, 8 * sigma]


def moment(order, weighted):
    return sum(
        (rates[k] if weighted else 1)
        * signs[k]
        * J
        * ((k + 1) ** (order + 1) - k ** (order + 1))
        * h ** (order + 1)
        / F(order + 1)
        for k in range(4)
    )


raw = [moment(k, False) for k in range(3)]
weighted = [moment(k, True) for k in range(3)]
assert raw[0] == raw[1] == 0
assert raw[2] == 4 * J * h**3
assert weighted[0] == -8 * sigma * J * h
assert weighted[1] == -16 * sigma * J * h * h
# A toy counterexample to importing error-sign alternation blindly: both
# errors are -1 at c0, but the absolute-value slopes are -1 and +2.
weight = F(2, 3)
assert weight * (-1) + (1 - weight) * 2 == 0
assert weight * 1 + (1 - weight) * 1 == 1
result = {
    "reference_jerk_moments": [str(v) for v in raw],
    "rate_weighted_jerk_moments": [str(v) for v in weighted],
    "admissible_piecewise_rate": [str(v) for v in rates],
    "nominal_c_raw_residual_impulse": str(F(1, 10) * weighted[0] - raw[0]),
    "zero_c_raw_residual_impulse": str(-raw[0]),
    "controller_unchanged": True,
    "toy_signed_slope_counterexample": {
        "errors": ["-1+c", "-1-2c"],
        "optimum": "c=0, peak=1",
        "both_errors_at_optimum": [-1, -1],
        "dual_weight": str(weight),
        "scope": "Abstract convex minimax example, not a replacement plant model.",
    },
    "limits": "Declared piecewise-constant rate probe in original band. Exact integral of external forcing (rc−1)j with w0 only, not integral of complete e-triple-prime: feedback omitted from this channel diagnostic. Neither zero forcing impulse nor low impulse proves small peak position error.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
