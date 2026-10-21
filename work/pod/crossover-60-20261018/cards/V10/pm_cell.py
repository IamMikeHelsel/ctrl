"""Exact local Cayley-cell and cone-budget experiments, not a full search proof."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def cayley(a, b, c):
    den = 1 + a * a + b * b + c * c
    rows = [
        [1 + a * a - b * b - c * c, 2 * (a * b - c), 2 * (a * c + b)],
        [2 * (a * b + c), 1 - a * a + b * b - c * c, 2 * (b * c - a)],
        [2 * (a * c - b), 2 * (b * c + a), 1 - a * a - b * b + c * c],
    ]
    return [[x / den for x in row] for row in rows]


def dot(a, b):
    return sum((x * y for x, y in zip(a, b, strict=True)), F(0))


def det(r):
    return (
        r[0][0] * (r[1][1] * r[2][2] - r[1][2] * r[2][1])
        - r[0][1] * (r[1][0] * r[2][2] - r[1][2] * r[2][0])
        + r[0][2] * (r[1][0] * r[2][1] - r[1][1] * r[2][0])
    )


def matvec(r, x):
    return [dot(row, x) for row in r]


points = [F(n, 800) for n in [-2, -1, 0, 1, 2]]
maximum = F(0)
for a, b, c in itertools.product(points, repeat=3):
    r = cayley(a, b, c)
    for i, j in itertools.product(range(3), repeat=2):
        assert dot(r[i], r[j]) == int(i == j)
    assert det(r) == 1
    frob2 = sum((r[i][j] - int(i == j)) ** 2 for i, j in itertools.product(range(3), repeat=2))
    s = a * a + b * b + c * c
    assert frob2 == 8 * s / (1 + s) <= F(1, 50) ** 2
    maximum = max(maximum, frob2)

# General pixel bounds for BOTH observations of the fixed-camera fixture.
gamma, delta, k_upper, m_upper = F(1, 10), F(1, 50), F(8, 5), F(3, 2)
u_upper = F(9, 8)
assert u_upper * u_upper >= F(5, 4)
assert m_upper * m_upper >= 1 + F(5, 4)
assert k_upper * k_upper >= 1 + (u_upper + gamma) ** 2
k = delta * k_upper
outer = (gamma + m_upper * k) / (1 - k)
assert k < 1 and outer == F(37, 242) < F(1, 4)

# Forgetting the residual linear-map norm M is not sound.
# For u=(-1,1/2), B_u h = (h_x+h_z,h_y-h_z/2).
h = [F(4), F(-2), F(5)]
bh = [h[0] + h[2], h[1] - h[2] / 2]
assert dot(bh, bh) == F(9, 4) * dot(h, h) > dot(h, h)

# Same extrinsic t is not same physical center when R changes.
r = cayley(F(0), F(0), F(1, 400))
x = [F(0), F(1000), F(0)]
rx = matvec(r, x)
t = [-rx[0], -rx[1], 1 - rx[2]]
true = [rx[i] + t[i] for i in range(3)]
nominal_wrong = [x[i] + t[i] for i in range(3)]
assert true == [0, 0, 1]
assert nominal_wrong == [F(800000, 160001), F(2000, 160001), 1]
assert nominal_wrong[0] > outer
# Correctly transport t0=R^T t, preserving C, giving v0=R^T true=e3.
rt = list(map(list, zip(*r, strict=True)))
t0 = matvec(rt, t)
nominal_correct = [x[i] + t0[i] for i in range(3)]
assert nominal_correct == [0, 0, 1]

# Distinguish a matrix norm from its square.
frob2 = sum((r[i][j] - int(i == j)) ** 2 for i, j in itertools.product(range(3), repeat=2))
probe = [F(1), F(0), F(0)]
change = [matvec(r, probe)[i] - probe[i] for i in range(3)]
assert dot(change, change) > frob2 * frob2

out = {
    "cayley_grid_count": 125,
    "orthogonal_determinant_checks": "all exact",
    "max_frobenius_squared": str(maximum),
    "delta_squared": str(delta * delta),
    "gamma": str(gamma),
    "outer_gamma": str(outer),
    "nominal_lower": "1/4",
    "residual_map_counterexample": {
        "input_norm_squared": str(dot(h, h)),
        "output_norm_squared": str(dot(bh, bh)),
    },
    "wrong_fixed_t": list(map(str, nominal_wrong)),
    "correct_same_center": list(map(str, nominal_correct)),
    "scope": "125 samples check implementation only; scalar polynomial universal helpers separate. Hand norm/depth bridge gives declared local cell exclusion, not whole SO3 cover or a physical camera certificate.",
}
(HERE / "pm_cell.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
