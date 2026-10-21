"""Declared constant-jerk probe; numerical evidence, different from saved move."""

import json
from pathlib import Path

import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize_scalar

ROOT = Path(__file__).resolve().parent
SIGMA = 1
RATES = (8, 12)
HORIZONS = (0.02, 0.08, 0.25, 1, 4, 12)


def response(t, r):
    # augmented constant-unit forcing, zero initial state
    matrix = np.array([[0.0, 1, 0, 0], [0, 0, 1, 0], [-8 * r, -6 * r, -1.5 * r, 1], [0, 0, 0, 0]])
    return float(expm(matrix * t)[0, 3])


rows = []
for horizon in HORIZONS:
    gains = []
    for rate in RATES:
        grid = np.linspace(0, horizon, 1001)
        values = [abs(response(t, rate)) for t in grid]
        k = int(np.argmax(values))
        refined = minimize_scalar(
            lambda t, rate=rate: -abs(response(t, rate)),
            bounds=(grid[max(0, k - 1)], grid[min(len(grid) - 1, k + 1)]),
            method="bounded",
            options={"xatol": 1e-13},
        )
        gains.append(max(values[k], -float(refined.fun)))
    f, g = gains
    c = (f + g) / (8 * f + 12 * g)

    def objective(k, f=f, g=g):
        return max(f * abs(8 * k - 1), g * abs(12 * k - 1))

    rows.append(
        {
            "T": horizon,
            "peak_gains": gains,
            "endpoint_gains": [response(horizon, r) for r in RATES],
            "peak_minimax_c": c,
            "peak_optimum": objective(c),
            "nominal": objective(0.1),
            "cube": objective(5 / 48),
            "zero": objective(0),
        }
    )
# Independent exact closed form at lower rate, within floating tolerance only.
checks = [
    abs(response(t, 8) - (1 - np.exp(-4 * t) * (1 + 4 * t + 8 * t * t)) / 64)
    for t in (0.02, 0.08, 0.25, 1, 4)
]
assert max(checks) < 1e-14
result = {
    "scenario": "unit constant jerk, sigma1, w0, zero errors; two constant rates8/12 only",
    "rows": rows,
    "closed_form_check_max_error": max(checks),
    "scope": "Numerical optimized finite-time maxima, not interval bounds or all admissible rates. Peak and endpoint objectives explicitly differ.",
}
(ROOT / "pm_step_probe.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
