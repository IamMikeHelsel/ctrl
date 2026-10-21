"""Independently test tangent Jacobians with exact rational Cayley rotations."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

P = Path(__file__).parent
s = json.loads((P / "inventor_exact.json").read_text())


def mat(a):
    return [[F(x) for x in row] for row in a]


def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def skew(t):
    return [[0, -t[2], t[1]], [t[2], 0, -t[0]], [-t[1], t[0], 0]]


def residual(r, t, x, y):
    e = mm(skew(t), r)
    return sum(y[i] * e[i][j] * x[j] for i, j in product(range(3), repeat=2))


def rotation(axis, h):
    q = [[F(i == j) for j in range(3)] for i in range(3)]
    i, j = [k for k in range(3) if k != axis]
    sign = -1 if axis == 1 else 1
    q[i][i] = q[j][j] = (1 - h * h) / (1 + h * h)
    q[i][j] = -sign * 2 * h / (1 + h * h)
    q[j][i] = sign * 2 * h / (1 + h * h)
    return q


checks = 0
for pose, jac in zip([s["pose_A"], s["pose_B"]], s["jacobians"], strict=True):
    r, t = mat(pose["R"]), list(map(F, pose["t"]))
    for point, row in zip(s["scene"], jac["full_six_matrix"], strict=True):
        x, y = list(map(F, point["x1"])), list(map(F, point["x2"]))
        assert residual(r, t, x, y) == 0
        for axis in range(3):
            for h in [F(1, 7), F(1, 3), F(2)]:
                positive = residual(mm(rotation(axis, h), r), t, x, y)
                negative = residual(mm(rotation(axis, -h), r), t, x, y)
                # Cayley parameter angle has derivative2 at zero. Exact odd
                # part removes even term without numerical differentiation.
                derived = (1 + h * h) * (positive - negative) / (4 * h)
                assert derived == F(row[3 + axis])
                checks += 1
            tt = t.copy()
            tt[axis] += F(2, 7)
            assert (residual(r, tt, x, y) - residual(r, t, x, y)) / F(2, 7) == F(row[axis])
            checks += 1
out = {
    "exact_derivative_checks": checks,
    "method": "Exact Cayley odd-part rotational derivative and independent translation finite differences",
    "scope": "Confirms displayed epipolar tangent Jacobians; does not prove global uniqueness or cover all poses.",
}
(P / "pm_derivative.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
