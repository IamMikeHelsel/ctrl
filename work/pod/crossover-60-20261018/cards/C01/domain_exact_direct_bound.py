"""Rational inequalities supporting an analytic direct actual-jerk bound.

Requires independently checked frozen reference |j(t)|<=10.
"""

import json
import math
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def series(x, n):
    return sum((x**i / math.factorial(i) for i in range(n + 1)), F(0))


def main():
    assert F(5, 3) ** 2 < 3 < F(7, 4) ** 2
    assert series(F(5, 4), 5) > F(10, 3)
    assert series(F(14, 3), 8) > 64
    first_lobe_bound = F(3, 4) * F(3, 10)
    second_lobe_bound = F(11, 4) * F(1, 64)
    assert first_lobe_bound < 1 and second_lobe_bound < 1
    negative_area_bound = (first_lobe_bound + second_lobe_bound) / 6
    input_l1_bound = 1 + 2 * negative_area_bound
    actual_jerk_bound = 10 * input_l1_bound + F(4, 5)
    assert actual_jerk_bound < F(59, 5) < F(119, 10)
    out = {
        "evidence": "rational checks supporting analytic convolution bound; not Lean",
        "assumption": "frozen reference absolute jerk <=10 at all times",
        "negative_impulse_area_upper": str(negative_area_bound),
        "reference_to_actual_jerk_l1_upper": str(input_l1_bound),
        "disturbance_jerk_upper": "4/5",
        "direct_absolute_actual_jerk_upper": str(actual_jerk_bound),
        "direct_bound_float": float(actual_jerk_bound),
        "co_design_actual_jerk_lower_from_other_script": "119/10",
        "strict_gap_lower": str(F(119, 10) - actual_jerk_bound),
    }
    (HERE / "domain_exact_direct_bound_results.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
