"""Exact periodic response of ramp controller to bounded abstract tracking residual."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def solve(a, b):
    m = [row[:] + [v] for row, v in zip(a, b, strict=True)]
    for k in range(len(m)):
        p = next(i for i in range(k, len(m)) if m[i][k])
        m[k], m[p] = m[p], m[k]
        v = m[k][k]
        m[k] = [x / v for x in m[k]]
        for i in range(len(m)):
            if i != k:
                v = m[i][k]
                m[i] = [x - v * y for x, y in zip(m[i], m[k], strict=True)]
    return [row[-1] for row in m]


patterns = [[0, 1, 1, 1, 0, -1, -1, -1], [1] * 10 + [-1] * 10, [1, -1]]
for half in (5, 10, 20, 30):
    patterns.append(
        [F(i, half) for i in range(-half, half)] + [F(i, half) for i in range(half, -half, -1)]
    )
rows = []
for pattern in patterns:
    n = len(pattern)
    eta = [F(23, 5000) * v for v in pattern]
    a = [[F(0) for _ in pattern] for _ in pattern]
    b = []
    for k in range(n):
        a[k][(k + 1) % n] += 1
        a[k][k] -= 1
        a[k][(k - 1) % n] += F(1, 10)
        a[k][(k - 2) % n] += F(1, 10)
        b.append(-(eta[(k - 1) % n] + eta[(k - 2) % n]) / 10)
    x = solve(a, b)
    y = [u + v for u, v in zip(x, eta, strict=True)]
    v = [-10 * y[(k - 1) % n] for k in range(n)]
    accel = [(v[k] - v[(k - 1) % n]) * 50 for k in range(n)]
    for k in range(n):
        assert x[(k + 1) % n] == x[k] - (y[(k - 1) % n] + y[(k - 2) % n]) / 10
    rows.append(
        {
            "pattern": [str(t) for t in pattern],
            "eta_bound": str(max(map(abs, eta))),
            "x": [str(t) for t in x],
            "y": [str(t) for t in y],
            "peak_actual_target_error": str(max(map(abs, y))),
            "peak_reference_speed": str(max(map(abs, v))),
            "peak_reference_accel": str(max(map(abs, accel))),
            "target_5mrad_pass": max(map(abs, y)) <= F(1, 200),
            "ramp_accel_1_pass": max(map(abs, accel)) <= 1,
        }
    )
out = {
    "scope": "Counterexample search to composition from eta amplitude bound ALONE. Abstract periodic residual need not be realizable by the declared physical inner ODE/age/noise model. No physical counterexample claimed. Exact periodic histories, not zero-state transients.",
    "rows": rows,
}
(HERE / "pm_perturb.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps([{k: v for k, v in r.items() if k not in ("x", "y")} for r in rows], indent=2))
