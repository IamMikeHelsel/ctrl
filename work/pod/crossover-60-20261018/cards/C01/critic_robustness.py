"""Independent physical-state integration of the relocated reference filter."""

import json
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

BASE = Path(__file__).parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)


def replay(gain, rate, disturbance):
    state = np.zeros(4)
    peaks = np.zeros(2)
    tv = 0.0
    ji = 0.0
    for phase in json.loads(SOURCE.read_text()):
        start, end = [float(F(phase[k])) for k in ["start", "end"]]
        polys = [[float(F(c)) for c in phase["position_coefficients_local_time"]]]
        for _ in range(4):
            polys.append([i * c for i, c in enumerate(polys[-1])][1:] or [0.0])

        def output(t, z, start=start, polys=polys):
            q, qv, qa, j, snap = [np.polynomial.polynomial.polyval(t - start, p) for p in polys]
            x, v, a, f = z
            u = qa - 800 * (x - q) - 60 * (v - qv) - 0.5 * (a - qa) + j / 96 + gain * f
            jerk = rate * (u + disturbance - a)
            fd = 20 * (j - f)
            ud = j - 800 * (v - qv) - 60 * (a - qa) - 0.5 * (jerk - j) + snap / 96 + gain * fd
            return x - q, jerk, ud, fd

        def rhs(t, z, output=output):
            _, jerk, _, fd = output(t, z)
            return [z[1], z[2], jerk, fd]

        sol = solve_ivp(
            rhs,
            (start, end),
            state,
            method="DOP853",
            rtol=1e-12,
            atol=1e-14,
            max_step=0.001,
            dense_output=True,
        )
        if not sol.success:
            raise ValueError(sol.message)
        n = int(np.ceil((end - start) / 0.00005))
        times = np.linspace(start, end, n + 1)
        values = np.array([output(t, sol.sol(t)) for t in times])
        peaks = np.maximum(peaks, np.max(np.abs(values[:, :2]), axis=0))
        h = (end - start) / n
        tv += h * (np.abs(values[:-1, 2]).sum() + np.abs(values[1:, 2]).sum()) / 2
        ji += h * ((values[:-1, 1] ** 2).sum() + (values[1:, 1] ** 2).sum()) / 2
        state = sol.y[:, -1]
    return dict(error=peaks[0], peakjerk=peaks[1], tv_excluding_jump=tv, jerk_squared_integral=ji)


rows = json.loads((BASE / "inventor_robustness.json").read_text())["refined"]
out = []
for row in rows:
    results = []
    for gain, key in [(0, "direct"), (1 / 960, "relocated_fixed_g_1_over_960")]:
        found = replay(gain, row["actuator_rate"], row["disturbance"])
        expected = row[key]
        target = [
            expected["peak_error_m"],
            expected["peak_actual_jerk"],
            expected["command_TV_including_initial_jump"] - 10 / 96,
            expected["actual_jerk_squared_integral"],
        ]
        diff = max(abs(a - b) for a, b in zip(found.values(), target, strict=True))
        if diff > 1e-7:
            raise ValueError(diff)
        results.append(dict(gain=gain, maximum_difference=diff, result=found))
    out.append(dict(rate=row["actuator_rate"], disturbance=row["disturbance"], cases=results))
(BASE / "critic_robustness_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
