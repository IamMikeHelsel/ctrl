"""Continuous exact Taylor enclosures for unchanged short reference, fixed source rates.
No sampled-peak acceptance, no state reset at joins, no numerical simulator import.
"""

import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

SCALE = 10**100
TAIL = F(1, 10**80)
DT = F(1, 100)


def ceil(q):
    return -((-q.numerator) // q.denominator)


def point(q):
    q = F(q) * SCALE
    return q.numerator // q.denominator, ceil(q)


def mul(c, box):
    c = F(c)
    lo, hi = box if c >= 0 else reversed(box)
    return c.numerator * lo // c.denominator, -((-c.numerator * hi) // c.denominator)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def matrix(r, k, jerk):
    # [ex, ev, ea, exp(-20t), 1]. W=1/2000, sigma=1.
    return [
        [F(0), F(1), F(0), F(0), F(0)],
        [F(0), F(0), F(1), F(0), F(0)],
        [-8 * r, -6 * r, -F(3, 2) * r, r / F(2000), (r * k - 1) * jerk - r / F(2000)],
        [F(0), F(0), F(0), F(-20), F(0)],
        [F(0)] * 5,
    ]


def step(A, initial):
    M = [[DT * c for c in row] for row in A]
    a = max(sum(abs(c) for c in row) for row in M)
    norm = F(max(abs(v) for box in initial for v in box), SCALE)
    total, term, scalar = list(initial), list(initial), F(1)
    # All intermediate times t in[0,DT]: initial+sum(theta^n term_n),theta in[0,1].
    tube = list(initial)
    for n in range(1, 500):
        nxt = []
        for row in M:
            summands = [mul(c, x) for c, x in zip(row, term, strict=True)]
            nxt.append(mul(F(1, n), (sum(x[0] for x in summands), sum(x[1] for x in summands))))
        term = nxt
        total = [add(x, y) for x, y in zip(total, term, strict=True)]
        tube = [add(x, (min(0, y[0]), max(0, y[1]))) for x, y in zip(tube, term, strict=True)]
        scalar *= a / n
        if a < n + 2:
            tail = norm * scalar * a / (n + 1) / (1 - a / (n + 2))
            if tail < TAIL:
                pad = ceil(tail * SCALE)
                return (
                    [(lo - pad, hi + pad) for lo, hi in total],
                    [(lo - pad, hi + pad) for lo, hi in tube],
                    n,
                    pad,
                )
    raise AssertionError("Degree cap")


def decimal_box(box, digits=12):
    g = 10**digits
    return [str(F(box[0] * g // SCALE, g)), str(F(-((-box[1] * g) // SCALE), g))]


def run(r, k):
    state = [point(0)] * 3 + [point(1), point(1)]
    records, peak, max_degree = [], 0, 0
    for i in range(408):
        j = (10, -10, -10, 10)[i // 2] if i < 8 else 0
        initial = state
        state, tube, degree, pad = step(matrix(F(r), k, F(j)), initial)
        bound = max(abs(tube[0][0]), abs(tube[0][1]))
        peak = max(peak, bound)
        max_degree = max(max_degree, degree)
        records.append(
            {
                "start": str(i * DT),
                "jerk": j,
                "position_tube": decimal_box(tube[0]),
                "endpoint": [decimal_box(x) for x in state[:3]],
                "initial": [decimal_box(x) for x in initial[:3]],
                "degree": degree,
                "tail_grid_units": str(pad),
            }
        )
    upper = F(ceil(F(peak, SCALE) * 10**12), 10**12)
    radius = (F(1, 2000) + 10 * max(abs(k - F(1, 8)), abs(k - F(1, 12)))) / 2
    return {
        "fixed_rate": r,
        "kappa": str(k),
        "continuous_position_bound_m": str(upper),
        "less_than_point2mm": upper < F(1, 5000),
        "global_cube_radius_m": str(radius),
        "max_degree": max_degree,
        "cells": records,
    }


if __name__ == "__main__":
    results = []
    for k in (F(0), F(1, 10), F(5, 48)):
        for r in (8, 10, 12):
            result = run(r, k)
            results.append(result)
            print({k: v for k, v in result.items() if k != "cells"}, flush=True)
    payload = {
        "scope": "Exact continuous finite-horizon enclosure for each named fixed rate and the saved exponential disturbance; NOT arbitrary r(t) or arbitrary bounded w(t).",
        "reference": {
            "jerks": [10, -10, -10, 10],
            "phase_duration": "1/50",
            "hold_duration": "4",
            "final_position": "1/6250",
        },
        "horizon": "102/25",
        "step": str(DT),
        "grid_digits": 100,
        "tail_target": str(TAIL),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "results": results,
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(payload, indent=2) + "\n")
