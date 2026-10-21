"""Frozen-task numerical screen of causal polynomial snap feedforward."""

import json
import math
from fractions import Fraction as F
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)


def deriv(p):
    return [i * p[i] for i in range(1, len(p))] or [0.0]


def value(p, t):
    return sum(c * t**i for i, c in enumerate(p))


def rhs(y, j, snap, k, l, direct):
    e, ev, ea, w = y
    if direct:
        ej = -64000 * e - 4800 * ev - 120 * ea + (80 * k - 1) * j + 0.8
        ud = j - 800 * ev - 60 * ea - 0.5 * ej + k * snap
        return [ev, ea, ej, 0], ej + j, ud
    ej = -80 * ea + 80 * w + 0.8 - j
    wd = -16000 * e - 1200 * ev - 10 * ea - 20 * w + (20 * k - 1) * j + 20 * l * snap
    return [ev, ea, ej, wd], ej + j, wd + j


def run(k, l, direct, step, samples=False):
    trace = []
    y = [0.0] * 4
    peak = 0
    peakt = 0
    jerk2 = 0
    tv = 10 / 96 if direct else 0
    maxjerk = 0
    for ph in json.loads(SOURCE.read_text()):
        start, end = float(F(ph["start"])), float(F(ph["end"]))
        p = list(map(lambda x: float(F(x)), ph["position_coefficients_local_time"]))
        jp = deriv(deriv(deriv(p)))
        sp = deriv(jp)
        n = math.ceil((end - start) / step)
        h = (end - start) / n
        for z in range(n):
            t = z * h
            f, j0, u0 = rhs(y, value(jp, t), value(sp, t), k, l, direct)
            y1 = [a + h * b / 2 for a, b in zip(y, f, strict=True)]
            f1, _, _ = rhs(y1, value(jp, t + h / 2), value(sp, t + h / 2), k, l, direct)
            y2 = [a + h * b / 2 for a, b in zip(y, f1, strict=True)]
            f2, _, _ = rhs(y2, value(jp, t + h / 2), value(sp, t + h / 2), k, l, direct)
            y3 = [a + h * b for a, b in zip(y, f2, strict=True)]
            f3, _, _ = rhs(y3, value(jp, t + h), value(sp, t + h), k, l, direct)
            y = [
                a + h * (b + 2 * c + 2 * d + e) / 6
                for a, b, c, d, e in zip(y, f, f1, f2, f3, strict=True)
            ]
            _, j1, u1 = rhs(y, value(jp, t + h), value(sp, t + h), k, l, direct)
            jerk2 += h * (j0 * j0 + j1 * j1) / 2
            tv += h * (abs(u0) + abs(u1)) / 2
            maxjerk = max(maxjerk, abs(j0), abs(j1))
            if samples:
                trace.append([start + t + h, y[0], h, j0, j1, u0, u1])
            if abs(y[0]) > peak:
                peak = abs(y[0])
                peakt = start + t + h
    output = {
        "step": step,
        "peak_abs_error_m": peak,
        "peak_time_s": peakt,
        "sampled_tracking_pass": peak <= 0.0002,
        "actual_jerk_squared_integral": jerk2,
        "command_total_variation_including_initial_jump": tv,
        "peak_actual_jerk": maxjerk,
        "final_error_m": y[0],
    }

    if samples:
        output["trace"] = trace
    return output


results = {}
for name, k, l, direct in [
    ("direct", 1 / 96, 0, True),
    ("original", 1 / 96, 0, False),
    ("compensated", 29 / 480, 0, False),
    ("snap_compensated", 29 / 480, 1 / 1600, False),
]:
    results[name] = [run(k, l, direct, h) for h in [0.0002, 0.0001]]
Path(__file__).with_name("inventor_screen.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
