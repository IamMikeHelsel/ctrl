"""Exploratory changed architectures with frozen task and no disturbance oracle."""

import json
import math
from fractions import Fraction as F
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)


def der(p):
    return [i * p[i] for i in range(1, len(p))] or [0.0]


def val(p, t):
    return sum(c * t**i for i, c in enumerate(p))


def run(gain, cap, step, rate=80, disturbance=0.01):
    assert cap is None or rate == 80

    def field(y, j, snap):
        e, ev, ea, z = y
        zd = 20 * (j - z)
        delta = -800 * e - 60 * ev - 1.5 * ea + j / 96 + gain * z
        clipped = cap is not None and abs(delta) > cap / 80 - 0.01
        if clipped:
            delta = max(-cap / 80 + 0.01, min(cap / 80 - 0.01, delta))
        ej = rate * delta + rate * disturbance - j
        ud = (ej + j) if clipped else j - 800 * ev - 60 * ea - 0.5 * ej + snap / 96 + gain * zd
        return [ev, ea, ej, zd], ej + j, ud

    y = [0.0] * 4
    peak = 0
    pt = 0
    ji = 0
    tv = 10 / 96
    jpeak = 0
    for phase in json.loads(SOURCE.read_text()):
        start, end = float(F(phase["start"])), float(F(phase["end"]))
        p = [float(F(v)) for v in phase["position_coefficients_local_time"]]
        jp = der(der(der(p)))
        sp = der(jp)
        count = math.ceil((end - start) / step)
        dt = (end - start) / count
        for n in range(count):
            t = n * dt
            f0, j0, u0 = field(y, val(jp, t), val(sp, t))
            f1, _, _ = field(
                [a + dt * b / 2 for a, b in zip(y, f0, strict=True)],
                val(jp, t + dt / 2),
                val(sp, t + dt / 2),
            )
            f2, _, _ = field(
                [a + dt * b / 2 for a, b in zip(y, f1, strict=True)],
                val(jp, t + dt / 2),
                val(sp, t + dt / 2),
            )
            f3, _, _ = field(
                [a + dt * b for a, b in zip(y, f2, strict=True)], val(jp, t + dt), val(sp, t + dt)
            )
            y = [
                a + dt * (b + 2 * c + 2 * d + e) / 6
                for a, b, c, d, e in zip(y, f0, f1, f2, f3, strict=True)
            ]
            _, j1, u1 = field(y, val(jp, t + dt), val(sp, t + dt))
            ji += dt * (j0 * j0 + j1 * j1) / 2
            tv += dt * (abs(u0) + abs(u1)) / 2
            jpeak = max(jpeak, abs(j0), abs(j1))
            if abs(y[0]) > peak:
                peak = abs(y[0])
                pt = start + t + dt
    return {
        "gain": gain,
        "robust_jerk_cap": cap,
        "step": step,
        "peak_error_m": peak,
        "peak_error_time": pt,
        "actual_jerk_squared_integral": ji,
        "command_TV_including_initial_jump": tv,
        "peak_actual_jerk": jpeak,
        "sampled_tracking_pass": peak <= 0.0002,
    }


results = {
    "relocated_feedforward_filter": [
        run(g, None, h) for g in [0, 1 / 960, 1 / 480, 1 / 320] for h in [0.0002, 0.0001]
    ],
    "robust_jerk_cap": [run(0, 10.2, h) for h in [0.0002, 0.0001]],
}
Path(__file__).with_name("inventor_relocated.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
