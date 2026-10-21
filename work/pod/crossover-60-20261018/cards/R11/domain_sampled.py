"""Exact alternating-series enclosures for the predeclared delayed ZOH toy."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

CARD = Path(__file__).resolve().parent
a, h, delay, speed, n = F(40), F(1, 1000), F(1, 500), F(1), 80
x = a * h
# Alternating exponential series: x=1/25, terms strictly decreasing.
lo = sum(((-x) ** k / factorial(k) for k in range(32)), F(0))
hi = sum(((-x) ** k / factorial(k) for k in range(31)), F(0))
assert 0 < lo < hi < 1
cases = []
for label, missing in [
    ("coordinated", F(0)),
    ("no_rate_feedforward", F(1)),
    ("wrong_rate_sign", F(2)),
]:

    def equilibrium(e, missing=missing):
        return speed * (delay + h / (1 - e) + (missing - 1) / a)

    lower = equilibrium(lo) * (1 - hi**n)
    upper = equilibrium(hi) * (1 - lo**n)
    assert 0 <= lower <= upper
    if label == "coordinated":
        assert upper < F(1, 200)
    else:
        assert lower > F(1, 200)
    cases.append(
        {
            "case": label,
            "e_at_80th_release_interval": [
                str(F((lower.numerator * 10**12) // lower.denominator, 10**12)),
                str(F(-((-upper.numerator * 10**12) // upper.denominator), 10**12)),
            ],
            "rad_interval_decimal_for_display": [float(lower), float(upper)],
            "exact_threshold_decision": "pass" if upper < F(1, 200) else "fail",
        }
    )
report = {
    "parameters": {
        "a": str(a),
        "h": str(h),
        "delay": str(delay),
        "base_rate": str(speed),
        "initial_time": str(delay),
        "initial_q": str(-speed * delay),
        "initial_world_error": "0",
        "world_goal": "0",
        "disturbance": "0",
        "N": n,
        "evaluation_time": str(delay + n * h),
    },
    "hold_command": "c_n=-v*n*h+(missing-1)*v/a; released at n*h+delay",
    "recurrence": "e_(n+1)=E*e_n+v*((delay+(missing-1)/a)*(1-E)+h)",
    "equilibrium": "v*(delay+h/(1-E)+(missing-1)/a)",
    "exp_interval": [str(lo), str(hi)],
    "cases": cases,
    "evidence": "Exact rational enclosure of analytic recurrence. ODE-to-recurrence derivation hand checked, not Lean certified. Same retained physical state for all variants.",
}
(CARD / "domain_sampled.json").write_text(json.dumps(report, indent=2) + "\n")
print(
    json.dumps(
        {
            "cases": [
                {k: v for k, v in c.items() if k != "e_at_80th_release_interval"} for c in cases
            ]
        },
        indent=2,
    )
)
