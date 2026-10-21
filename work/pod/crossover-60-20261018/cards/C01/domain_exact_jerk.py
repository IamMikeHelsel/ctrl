"""Rational exp enclosure of actual jerk at t=1/20 for nominal inverse candidate.

A standalone arithmetic witness, not a Lean certificate or direct-baseline peak bound.
"""

import json
import math
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    c = F(16, 390625)
    p = [c, 25 * c, 625 * c / 2, 15625 * c / 6 + F(23, 15)]
    for _ in range(3):
        p = [(i + 1) * (p[i + 1] if i + 1 < len(p) else 0) - 25 * p[i] for i in range(len(p))]
    assert p == [F(46, 5), F(-706), F(9025), F(-25625)]
    t = F(1, 20)
    factor = -sum((coefficient * t**i for i, coefficient in enumerate(p)), F(0))
    assert factor == F(2157, 320)
    x = 25 * t
    n = 12
    partial = sum((x**i / math.factorial(i) for i in range(n + 1)), F(0))
    remainder = x ** (n + 1) / math.factorial(n + 1) / (1 - x / (n + 2))
    low = 10 + factor / (partial + remainder)
    high = 10 + factor / partial
    assert low > F(119, 10)
    out = {
        "evidence": "analytic derivative, rational exponential enclosure; no Lean proof",
        "time": str(t),
        "reference_jerk": "10",
        "actual_jerk_expression": "10 + (2157/320)*exp(-5/4)",
        "actual_jerk_lower": str(low),
        "actual_jerk_upper": str(high),
        "lower_float": float(low),
        "upper_float": float(high),
        "exact_strict_lower_claim": ">119/10",
        "limitation": "alone does not bound the continuous-time direct baseline peak",
    }
    (HERE / "domain_exact_jerk_results.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
