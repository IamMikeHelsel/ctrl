"""Independent physical-coordinate exact Taylor checker; no producer imports."""

import json
import math
from fractions import Fraction as F
from pathlib import Path

Q = 10**70
N = 60


def ceil(x):
    return -((-x.numerator) // x.denominator)


def image(c, b):
    l, u = b if c >= 0 else (b[1], b[0])
    return c.numerator * l // c.denominator, -((-c.numerator * u) // c.denominator)


def matrix(r, k, j, W=F(1, 2000)):
    # Physical [x,v/4,a/16,q,q'/4,q''/16,exp(-20t),1].
    A = [[F(0) for _ in range(8)] for _ in range(8)]
    A[0][1] = A[1][2] = A[3][4] = A[4][5] = F(4)
    A[2] = [
        r * c
        for c in (
            F(-1, 2),
            F(-3, 2),
            F(-3, 2),
            F(1, 2),
            F(3, 2),
            F(3, 2),
            W / 16,
            (k * j - W) / 16,
        )
    ]
    A[5][7] = j / 16
    A[6][6] = F(-20)
    return A


def advance(A, s, dt):
    M = [[dt * x for x in row] for row in A]
    a = max(sum(map(abs, row)) for row in M)
    b = F(max(abs(v) for row in s for v in row), Q)
    assert a < N + 2
    tail = b * a ** (N + 1) / math.factorial(N + 1) / (1 - a / F(N + 2))
    pad = ceil(tail * Q)
    term = s
    total = [list(x) for x in s]
    error = [s[0][0] - s[3][1], s[0][1] - s[3][0]]
    for n in range(1, N + 1):
        term = [
            tuple(
                sum(image(c / F(n), v)[side] for c, v in zip(row, term, strict=True))
                for side in (0, 1)
            )
            for row in M
        ]
        for i in range(8):
            total[i][0] += term[i][0]
            total[i][1] += term[i][1]
        lo, hi = term[0][0] - term[3][1], term[0][1] - term[3][0]
        error[0] += min(0, lo)
        error[1] += max(0, hi)
    return [(l - pad, u + pad) for l, u in total], (error[0] - 2 * pad, error[1] + 2 * pad)


def run(k, rates, witness=F(237, 500), reset=False, horizon=F(102, 25), W=F(1, 2000)):
    s = [(0, 0)] * 6 + [(Q, Q), (Q, Q)]
    t = F(0)
    peak = 0
    motion_peak = 0
    at_witness = None
    while t < horizon:
        phase = min(int(t / F(1, 50)), 4)
        j = F((10, -10, -10, 10, 0)[phase])
        r = F(rates[phase])
        dt = min(F(1, 100), horizon - t)
        if t < witness < t + dt:
            dt = witness - t
        if t < F(2, 25):
            dt = min(dt, (phase + 1) * F(1, 50) - t)
        if reset and t in (F(1, 50), F(1, 25), F(3, 50), F(2, 25)):
            s[:3] = s[3:6]
        s, tube = advance(matrix(r, k, j, W), s, dt)
        peak = max(peak, abs(tube[0]), abs(tube[1]))
        t += dt
        if t <= F(2, 25):
            motion_peak = max(motion_peak, abs(tube[0]), abs(tube[1]))
        if t == witness:
            at_witness = [str(F(s[0][0] - s[3][1], Q)), str(F(s[0][1] - s[3][0], Q))]
    return {
        "kappa": str(k),
        "evaluated_horizon_s": str(horizon),
        "original_task_horizon_s": "102/25",
        "disturbance_bound_W": str(W),
        "disturbance_waveform": "-W*(1-exp(-20*t))",
        "final_error_field_scope": "Endpoint of evaluated_horizon_s, not necessarily original task horizon",
        "rates": rates,
        "continuous_upper": str(F(peak, Q)),
        "continuous_upper_mm_float": float(F(peak, Q) * 1000),
        "motion_upper_mm_float": float(F(motion_peak, Q) * 1000),
        "witness_time": str(witness),
        "witness": at_witness,
        "final_error_mm_float": float(F(s[0][0] - s[3][1], Q) * 1000),
        "reset": reset,
    }


if __name__ == "__main__":
    out = []
    for k in (F(0), F(1, 10), F(5, 48)):
        for r in (8, 10, 12):
            item = run(k, [r] * 5)
            out.append(item)
            print(k, r, item["continuous_upper_mm_float"], flush=True)
    for k, rates in ((F(0), [12, 12, 8, 8, 10]), (F(5, 48), [12, 8, 8, 12, 10])):
        out.append(run(k, rates))
    out.append(run(F(0), [12, 12, 8, 8, 10], reset=True))
    assert F(out[-3]["witness"][0]) > F(1, 5000)
    assert F(out[-2]["witness"][0]) > F(1, 5000)
    assert F(out[-1]["witness"][1]) < F(1, 5000)
    # Negative multiplier must reverse endpoints; a truncation without tail is not exp.
    assert image(F(-3, 2), (2, 5)) == (-8, -3)
    assert sum(F(1, math.factorial(n)) for n in range(N + 1)) < F(3)
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
