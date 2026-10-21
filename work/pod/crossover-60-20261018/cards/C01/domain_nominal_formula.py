"""Exact coefficient and rational exponential enclosure for nominal inverse tracking.

Analytic derivation plus exact rational arithmetic, not a Lean certificate.
"""

import csv
import json
import math
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    t = F(23, 205)
    x = 25 * t
    c = F(16, 390625)
    s3 = sum((x**n / math.factorial(n) for n in range(4)), F(0))
    multiplier = c * s3 + F(23, 15) * t**3
    n = 40
    partial = sum((x**i / math.factorial(i) for i in range(n + 1)), F(0))
    first_omitted = x ** (n + 1) / math.factorial(n + 1)
    remainder_bound = first_omitted / (1 - x / (n + 2))
    exp_negative_lower = 1 / (partial + remainder_bound)
    exp_negative_upper = 1 / partial
    error_lower = c - multiplier * exp_negative_upper
    error_upper = c - multiplier * exp_negative_lower
    assert -F(1, 5000) < error_lower <= error_upper < 0 < c < F(1, 5000)
    assert F(246) * t - F(138, 5) == 0
    errors = []
    with (HERE / "domain_retuned_fine_quad25_nominal.csv").open() as stream:
        for row in csv.DictReader(stream):
            time = float(F(row["t"]))
            z = 25 * time
            prediction = float(c) * (1 - math.exp(-z) * (1 + z + z * z / 2 + z**3 / 6)) - (
                23 / 15
            ) * time**3 * math.exp(-z)
            errors.append(abs(prediction - float(row["ex"])))
    out = {
        "evidence": "analytic formula and rational interval arithmetic; not kernel proof",
        "stationary_time": str(t),
        "steady_error_m": str(c),
        "minimum_error_lower": str(error_lower),
        "minimum_error_upper": str(error_upper),
        "minimum_error_mm_float": 1000 * float((error_lower + error_upper) / 2),
        "strict_tracking_margin_lower_m": str(F(1, 5000) + error_lower),
        "exponential_series_terms": n + 1,
        "max_difference_from_independent_augmented_exponential_m": max(errors),
        "assumptions": [
            "r=80, lambda=20, constant disturbance +.01, frozen reference jerk continuous",
            "gains p=15625/64,d=625/16,h=43/32,k=1/16,l=1/1600",
            "initial e=e'=e''=u=0; jerk reference initially 10",
            "exact continuous controller; no saturation or sampled implementation",
        ],
    }
    (HERE / "domain_nominal_formula_results.json").write_text(json.dumps(out, indent=2) + "\n")
    print(out["minimum_error_mm_float"], max(errors), float(c) * 1000)


if __name__ == "__main__":
    main()
