"""Numerical screen only: original short task, piecewise endpoint response rates."""

import json
from itertools import product
from pathlib import Path

import numpy as np
from scipy.linalg import expm

P = Path(__file__).resolve().parent
W = 0.0005


def mat(r, k, j):
    a = np.zeros((5, 5))
    a[0, 1] = 1
    a[1, 2] = 1
    a[2, :] = [-8 * r, -6 * r, -1.5 * r, (r * k - 1) * j - r * W, r * W]
    a[4, 4] = -20
    return a


def scan(k):
    # Eight10ms chunks, unchanged four20ms jerk phases. Piecewise rate does not reset state.
    js = [10, 10, -10, -10, -10, -10, 10, 10]
    trans = {(r, j): expm(0.01 * mat(r, k, j)) for r in (8, 12) for j in (-10, 10)}
    sample = {
        (r, j): np.array([expm(t * mat(r, k, j))[0] for t in np.linspace(0, 0.01, 21)])
        for r in (8, 12)
        for j in (-10, 10)
    }
    hold = np.array([expm(t * mat(10, k, 0))[0] for t in np.linspace(0, 4, 2001)])
    best = None
    for rs in product((8, 12), repeat=8):
        y = np.array([0, 0, 0, 1, 1.0])
        peak = 0
        peak_t = 0
        for i, (r, j) in enumerate(zip(rs, js, strict=True)):
            vals = sample[r, j] @ y
            idx = int(np.argmax(abs(vals)))
            if abs(vals[idx]) > peak:
                peak = float(abs(vals[idx]))
                peak_t = i * 0.01 + idx * 0.0005
            y = trans[r, j] @ y
        vals = hold @ y
        idx = int(np.argmax(abs(vals)))
        if abs(vals[idx]) > peak:
            peak = float(abs(vals[idx]))
            peak_t = 0.08 + idx * 0.002
        if best is None or peak > best["peak_abs_error_m"]:
            best = {
                "rates": list(rs),
                "peak_abs_error_m": peak,
                "peak_time_s": peak_t,
                "end_move_error_state": y[:3].tolist(),
            }
    return {"kappa": k, "cases": 256, "best": best}


results = [scan(k) for k in (0, 0.1, 5 / 48)]
(P / "pm_schedule_scan.json").write_text(
    json.dumps(
        {
            "scope": "Numerical endpoint-schedule search, not continuous enclosure or arbitrary-rate proof",
            "W": W,
            "disturbance": "-W*(1-exp(-20t))",
            "jerk_phase_duration": 0.02,
            "horizon": 4.08,
            "results": results,
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(results))
