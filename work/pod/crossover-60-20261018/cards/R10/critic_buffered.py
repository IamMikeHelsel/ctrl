"""Independent buffered physical-acceleration witness; numerical, not a kernel proof."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import minimize_scalar

HERE = Path(__file__).resolve().parent
EVENTS = [(F(7, 25), F(1, 50), F(1, 5)), (F(17, 25), -F(1, 50), F(1, 5))]
knots = sorted({F(0), F(5, 2)} | {tau + i * h for tau, _, h in EVENTS for i in range(5)})
e = np.zeros(3)
best = {"absolute_acceleration": 0.0}
for left, right in zip(knots, knots[1:], strict=False):
    mid = (left + right) / 2
    ds = [
        sum(
            delta * c * (left - tau - i * h) ** (4 - k) / factorial(4 - k) / h**4
            for tau, delta, h in EVENTS
            for i, c in enumerate([1, -4, 6, -4, 1])
            if tau + i * h < mid
        )
        for k in range(5)
    ]
    ds = np.array(list(map(float, ds)))
    lo, hi = float(left), float(right)

    def rhs(t, x, ds=ds, lo=lo):
        j = ds[3] + ds[4] * (t - lo)
        return [x[1], x[2], -80 * (800 * x[0] + 60 * x[1] + 1.5 * x[2]) - j / 6 + 0.8]

    sol = solve_ivp(rhs, [lo, hi], e, method="DOP853", rtol=5e-13, atol=2e-15, dense_output=True)
    assert sol.success

    def actual_a(t, sol=sol, ds=ds, lo=lo):
        z = t - lo
        return sol.sol(t)[2] + ds[2] + ds[3] * z + ds[4] * z * z / 2

    grid = np.linspace(lo, hi, 501)
    values = [abs(actual_a(t)) for t in grid]
    k = int(np.argmax(values))
    candidate = minimize_scalar(
        lambda t: -abs(actual_a(t)),
        bounds=(grid[max(0, k - 1)], grid[min(500, k + 1)]),
        method="bounded",
        options={"xatol": 1e-14},
    )
    for t in [lo, hi, float(candidate.x)]:
        val = float(actual_a(t))
        if abs(val) > best["absolute_acceleration"]:
            z = t - lo
            best = {
                "time": t,
                "signed_actual_acceleration": val,
                "absolute_acceleration": abs(val),
                "reference_acceleration": float(ds[2] + ds[3] * z + ds[4] * z * z / 2),
                "tracking_acceleration_error": float(sol.sol(t)[2]),
            }
    e = sol.y[:, -1]
assert best["absolute_acceleration"] > 0.50006
result = {
    "rate": 80,
    "disturbance": 0.01,
    "witness": best,
    "scope": "DOP853 numerical witness from zero initial physical state, original buffered events retained; strict actual acceleration exceeds .5 despite conforming reference. Not an interval or Lean-certified physical inequality.",
}
(HERE / "critic_buffered.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
