"""Exact reference Bernstein bound supporting ordinary convolution estimate."""

import json
from fractions import Fraction as F
from math import comb
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)


def derivative(p):
    return [i * p[i] for i in range(1, len(p))] or [F(0)]


def bernstein_on(p, left, width):
    n = len(p) - 1
    power = [
        sum(p[j] * comb(j, i) * left ** (j - i) * width**i for j in range(i, n + 1))
        for i in range(n + 1)
    ]
    return [sum(power[i] * F(comb(k, i), comb(n, i)) for i in range(k + 1)) for k in range(n + 1)]


records = []
for phase in json.loads(SOURCE.read_text()):
    p = list(map(F, phase["position_coefficients_local_time"]))
    jerk = derivative(derivative(derivative(p)))
    duration = F(phase["end"]) - F(phase["start"])
    parts = 8
    for i in range(parts):
        left = duration * F(i, parts)
        width = duration / parts
        coefficients = bernstein_on(jerk, left, width)
        assert min(coefficients) >= -10 and max(coefficients) <= 10
        records.append(
            {
                "phase": phase["name"],
                "local_left": str(left),
                "width": str(width),
                "Bernstein_jerk_coefficients": list(map(str, coefficients)),
            }
        )
forcing = F(10, 6) + F(10, 12) + F(80, 100)
bound = forcing / F(40**3)
assert bound == F(33, 640000) and bound < F(1, 5000)
out = {
    "reference_jerk_bound": "10",
    "subinterval_certificates": records,
    "relocated_gain": "1/960",
    "nominal_rate": 80,
    "uncertain_disturbance_bound": "1/100",
    "slow_state_bound": "10",
    "forcing_bound": str(forcing),
    "convolution_kernel": "t^2 exp(-40 t)/2, t>=0",
    "kernel_L1_norm": "1/64000",
    "all_time_error_bound_m": str(bound),
    "scope": "Rational coefficient checks support an ordinary positive-convolution derivation. Neither ODE semantics nor convolution estimate is Lean-checked here; other rates and metric reduction remain numerical.",
}
Path(__file__).with_name("inventor_tracking_bound.json").write_text(
    json.dumps(out, indent=2) + "\n"
)
print(
    json.dumps(
        {
            "jerk_bound": 10,
            "subintervals": len(records),
            "error_bound_m": str(bound),
            "error_bound_mm": float(bound) * 1000,
            "tracking_target_m": "1/5000",
        },
        indent=2,
    )
)
