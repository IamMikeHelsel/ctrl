"""Independent DOP853 and derivative-root refinement of numerical Chebyshev fit."""

import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq, minimize_scalar

HERE = Path(__file__).parent
J, H, SIGMA, W = 10.0, 0.02, 1.0, 0.0005
NAMES = ["fixed8", "fixed10", "fixed12", "phase0", "phase1", "phase2", "phase3"]


def rvalue(t, name):
    if name.startswith("fixed"):
        return float(name[5:])
    return 10 - 2 * math.tanh(4 * math.cos(math.pi * t / (2 * H) + int(name[5:]) * math.pi / 2))


def integrate(name):
    initial = np.zeros(6)
    stages = []
    start = 0.0
    for duration, j in [(H, J), (H, -J), (H, -J), (H, J), (4.0, 0.0)]:

        def field(t, y, j=j):
            r = rvalue(t, name)
            b, v, a, z, zv, za = y
            return [
                v,
                a,
                r * (-8 * b - 6 * v - 1.5 * a - W * (-math.expm1(-20 * t))) - j,
                zv,
                za,
                r * (-8 * z - 6 * zv - 1.5 * za + j),
            ]

        sol = solve_ivp(
            field,
            (start, start + duration),
            initial,
            method="DOP853",
            rtol=2e-12,
            atol=2e-15,
            max_step=0.0005,
            dense_output=True,
        )
        assert sol.success
        times = np.linspace(start, start + duration, math.ceil(duration / 0.001) + 1)
        stages.append((sol.sol, times, sol.sol(times)))
        initial = sol.y[:, -1]
        start += duration
    return stages


traces = {name: integrate(name) for name in NAMES}


def extrema(c, name):
    values = []
    for sol, times, ys in traces[name]:
        velocities = ys[1] + c * ys[4]
        candidates = [times[0], times[-1]]
        for i in np.where(velocities[:-1] * velocities[1:] < 0)[0]:

            def vel(t, sol=sol):
                y = sol(t)
                return y[1] + c * y[4]

            candidates.append(brentq(vel, times[i], times[i + 1], xtol=1e-14))
        for t in candidates:
            y = sol(t)
            e = float(y[0] + c * y[3])
            values.append(
                {
                    "name": name,
                    "t": float(t),
                    "error": e,
                    "intercept": float(y[0]),
                    "slope": float(y[3]),
                }
            )
    return max(values, key=lambda v: abs(v["error"]))


def objective(c, names):
    return max(abs(extrema(c, n)["error"]) for n in names)


fit = minimize_scalar(
    lambda c: objective(c, NAMES[:4]),
    bounds=(-0.01, 0.02),
    method="bounded",
    options={"xatol": 1e-13},
)
c = float(fit.x)
active = [extrema(c, name) for name in NAMES]
base = json.loads((HERE / "inventor_minimax.json").read_text())["fine"]["optimum"]
# Candidate mismatch checks evaluate the same fine-grid c in a separate integrator.
comparison = {n: extrema(base["c_seconds"], n) for n in NAMES}
# Declaration: exchanging the held-out scenarios into training changes the finite game,
# never the reference, controller, initial condition, or 4.08s objective.
expanded = minimize_scalar(
    lambda v: objective(v, NAMES), bounds=(-0.01, 0.05), method="bounded", options={"xatol": 1e-13}
)
result = {
    "runtime": "Existing /usr/local/bin/python3 through uv; no packages installed",
    "original_horizon_s": 4.08,
    "original_four_rate_fit": {"c": c, "peak_m": float(fit.fun), "extrema": active},
    "independent_at_RK4_grid_coefficient": comparison,
    "expanded_seven_rate_fit": {
        "c": float(expanded.x),
        "peak_m": float(expanded.fun),
        "extrema": [extrema(float(expanded.x), n) for n in NAMES],
    },
    "limits": "Numerical DOP853 dense output plus sign-changing velocity root localization. No interval proof; root completeness not certified. Seven-rate result is an explicitly enlarged finite scenario game, not arbitrary-rate minimax.",
}
(HERE / "inventor_dense.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            "four_rate_c": c,
            "four_rate_peak_mm": float(fit.fun) * 1000,
            "expanded_c": float(expanded.x),
            "expanded_peak_mm": float(expanded.fun) * 1000,
            "heldout_peak_mm": max(abs(r["error"]) for r in active[4:]) * 1000,
        },
        indent=2,
    )
)
