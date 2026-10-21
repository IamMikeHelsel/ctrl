"""Exact rational projective/camera negatives; no producer geometry imports."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent
I = [[F(i == j) for j in range(3)] for i in range(3)]
Z = [F(0)] * 3


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def mv(A, x):
    return [dot(r, x) for r in A]


def add(a, b):
    return [x + y for x, y in zip(a, b, strict=True)]


def scale(c, x):
    return [c * y for y in x]


def det(A):
    return sum(
        (1 if (i, j, k) in [(0, 1, 2), (1, 2, 0), (2, 0, 1)] else -1) * A[0][i] * A[1][j] * A[2][k]
        for i, j, k in [(0, 1, 2), (1, 2, 0), (2, 0, 1), (0, 2, 1), (2, 1, 0), (1, 0, 2)]
    )


def cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def plane_H(R, t, n, d):
    return [[R[i][j] + t[i] * n[j] / d for j in range(3)] for i in range(3)]


def normalize(x):
    assert x[2] != 0
    return [y / x[2] for y in x]


# Positive depths and a nonzero first-plane offset do not force invertibility.
t = [F(-1), F(0), F(0)]
n = [F(1), F(0), F(0)]
H = plane_H(I, t, n, F(1))
assert det(H) == 0
X = [F(1), F(0), F(1)]
Y = [F(1), F(0), F(2)]
points = []
for p in [X, Y]:
    q = add(p, t)
    assert dot(n, p) == 1 and p[2] > 0 and q[2] > 0 and q != Z
    assert mv(H, p) == q
    points.append(
        {"X1": p, "X2": q, "ray1": normalize(p), "ray2": normalize(q), "depths": [p[2], q[2]]}
    )
assert points[0]["ray1"] != points[1]["ray1"] and points[0]["ray2"] == points[1]["ray2"]
# Source plane-through-first-center exclusion is essential: d0 inverse0 would drop translation.
np = [F(1), F(0), F(0)]
p = [F(0), F(0), F(1)]
tp = [F(1), F(0), F(0)]
assert dot(np, p) == 0 and mv(I, p) != add(p, tp)
# d2=0 remains permitted by the source algebra: a point can be the second center.
tzero = scale(F(-1), X)
Hzero = plane_H(I, tzero, n, F(1))
assert mv(Hzero, X) == Z and add(X, tzero) == Z
# Dropping nonzero rays/lines makes incidence trivial.
assert dot([F(1), F(2), F(3)], Z) == 0 and dot(Z, X) == 0
# Invertible H still can map a finite ray to infinity; nonzero is weaker than affine chart.
Hchart = [[F(0), F(0), F(1)], [F(0), F(1), F(0)], [F(1), F(0), F(0)]]
assert det(Hchart) == -1 and mv(Hchart, [F(0), F(0), F(1)]) == [F(1), F(0), F(0)]
# Projective negative scaling preserves incidences, not oriented positive-depth equations.
p = [F(0), F(0), F(1)]
minusI = [scale(F(-1), r) for r in I]
assert cross(mv(I, p), mv(minusI, p)) == Z and mv(minusI, p)[2] < 0
# Non-unit normal is legal for algebra; scaling n,d together leaves H unchanged.
t = [F(1), F(0), F(0)]
n = [F(0), F(0), F(2)]
H2 = plane_H(I, t, n, F(2))
assert H2 == plane_H(I, t, scale(F(3), n), F(6))
assert H2 != plane_H(I, t, scale(F(3), n), F(2))
# Planar epipolar incidence remains valid and nontrivial.
E = [[F(0), F(0), F(0)], [F(0), F(0), F(-1)], [F(0), F(1), F(0)]]
for u in [F(-1), F(0), F(1)]:
    for v in [F(-1), F(0), F(1)]:
        a = [u, v, F(1)]
        b = mv(H2, a)
        assert dot(b, mv(E, a)) == 0
assert dot([F(1), F(1), F(1)], mv(E, [F(0), F(0), F(1)])) == -1
results = {
    "second_center_plane_singularity": {"H": H, "points": points},
    "zero_depth_algebra": {"X": X, "t": tzero, "HX": Z},
    "finite_chart_failure": {"H": Hchart, "input": [0, 0, 1], "output": [1, 0, 0]},
    "negative_gauge": {
        "same_projective_point": True,
        "positive_depth_relation_preserved_without_transport": False,
    },
    "normal_gauge": {"joint_n_d_scaling_preserves": True, "normal_only_scaling_changes": True},
    "planar_epipolar": {"nine_valid_pairs": True, "arbitrary_wrong_correspondence_residual": -1},
    "scope": "Exact rational algebra and explicit physical normalized-camera fixtures; no pose-estimation uniqueness or noise claim.",
}
(P / "critic_geometry.json").write_text(json.dumps(results, default=str, indent=2) + "\n")
print(json.dumps(results, default=str))
