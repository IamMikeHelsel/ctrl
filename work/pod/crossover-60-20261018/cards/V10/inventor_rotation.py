"""Exact convex-hull SO(3) false feasibility, with an algebraic true optimum."""

import json
from fractions import Fraction as F
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions required")


def transpose(a):
    return [list(row) for row in zip(*a, strict=True)]


def multiply(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def determinant(a):
    return (
        a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
        - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
        + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
    )


identity = [[F(i == j) for j in range(3)] for i in range(3)]
rplus = [[F(3, 5), F(0), F(-4, 5)], [F(0), F(1), F(0)], [F(4, 5), F(0), F(3, 5)]]
rminus = [[-x for x in rplus[0]], [-x for x in rplus[1]], rplus[2].copy()]
for r in [rplus, rminus]:
    assert multiply(transpose(r), r) == identity
    assert multiply(r, transpose(r)) == identity
    assert determinant(r) == 1
    assert r[2][0] > 0 and r[2][2] > 0
    assert max(abs(r[0][0] / r[2][0]), abs(r[0][2] / r[2][2])) == F(4, 3)
mean = [[(rplus[i][j] + rminus[i][j]) / 2 for j in range(3)] for i in range(3)]
assert mean == [[0, 0, 0], [0, 0, 0], [F(4, 5), 0, F(3, 5)]]
assert determinant(mean) == 0
assert mean[2][0] > 0 and mean[2][2] > 0
assert all(mean[i][j] == 0 for i in [0, 1] for j in [0, 2])
# Thus known world points e1,e3, observed at(0,0), fixed camera center0,
# have positive-depth zero reprojection error at an explicit conv(SO3) point.


# Exact quadratic extension Q(sqrt2), no floating-point trigonometry.
class SqrtTwo:
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(self, other):
        other = other if isinstance(other, SqrtTwo) else SqrtTwo(other)
        return SqrtTwo(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return SqrtTwo(-self.a, -self.b)

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        other = other if isinstance(other, SqrtTwo) else SqrtTwo(other)
        return SqrtTwo(self.a * other.a + 2 * self.b * other.b, self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __eq__(self, other):
        other = other if isinstance(other, SqrtTwo) else SqrtTwo(other)
        return (self.a, self.b) == (other.a, other.b)


q = SqrtTwo(0, F(1, 2))  # sqrt2/2>0 by the positive-root convention
zero, one = SqrtTwo(0), SqrtTwo(1)
rstar = [[q, zero, -q], [zero, one, zero], [q, zero, q]]
assert multiply(transpose(rstar), rstar) == identity
assert multiply(rstar, transpose(rstar)) == identity
assert determinant(rstar) == 1
# Both depthsq>0. Pixel coordinates are(1,0),(-1,0); max Euclideanerror1.
assert rstar[0][0] == rstar[2][0]
assert rstar[0][2] == -rstar[2][2]
assert q * q == F(1, 2)
# Full-rank strengthened negative: observed pixels +/-1/10. A convex mixture
# of Rstar and diag(-1,-1,1)Rstar gives diag(.1,.1,1)Rstar, determinant1/100.
rstar_opposite = [[-x for x in rstar[0]], [-x for x in rstar[1]], rstar[2].copy()]
assert determinant(rstar_opposite) == 1
assert multiply(transpose(rstar_opposite), rstar_opposite) == identity
mixture = [
    [F(11, 20) * rstar[i][j] + F(9, 20) * rstar_opposite[i][j] for j in range(3)] for i in range(3)
]
assert determinant(mixture) == F(1, 100)
assert mixture[2][0] == q and mixture[2][2] == q
assert mixture[0][0] == F(1, 10) * mixture[2][0]
assert mixture[0][2] == -F(1, 10) * mixture[2][2]
assert mixture[1][0] == 0 and mixture[1][2] == 0
# True optimum9/10 follows by triangle inequality from original lower bound1;
# Rstar attains it. These finite checks verify the exact attaining matrices.
# Universal lower bound derivation: SO3 gives z1²+z3²<=1; pixel boundgamma
# and unit columns give1<=(1+gamma²)zj². Sum =>2<=1+gamma², hencegamma>=1.

out = {
    "status": "pass",
    "camera_center": [0, 0, 0],
    "known_points": [[1, 0, 0], [0, 0, 1]],
    "observations": [[0, 0], [0, 0]],
    "Rplus": [[str(x) for x in row] for row in rplus],
    "Rminus": [[str(x) for x in row] for row in rminus],
    "both_rational_endpoints_det": 1,
    "endpoint_max_error": "4/3",
    "convex_mean": [[str(x) for x in row] for row in mean],
    "mean_depths": ["4/5", "3/5"],
    "mean_determinant": 0,
    "mean_max_error": 0,
    "true_SO3_minimax_error": 1,
    "full_rank_extension": {
        "observations": [["1/10", "0"], ["-1/10", "0"]],
        "convex_weights": ["11/20", "9/20"],
        "relaxed_matrix": "diag(1/10,1/10,1) Rstar",
        "relaxed_determinant": "1/100",
        "relaxed_error": 0,
        "true_SO3_optimum": "9/10",
        "calibration_boundary": "Relaxation effectively permits a different focal scale",
    },
    "attainer": "[[q,0,-q],[0,1,0],[q,0,q]], q=positive sqrt2/2",
    "scope": "Fixed translation0; known point correspondences; Euclidean image-plane "
    "residual norm; positive depth. Exact arithmetic plus general lower-bound "
    "derivation, not a general rotation-search implementation.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
