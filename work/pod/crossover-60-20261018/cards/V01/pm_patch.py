"""Exact declared camera/patch fixture; no estimated camera or hardware claim."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

P = Path(__file__).resolve().parent
R = [[F(3, 5), F(0), F(4, 5)], [F(0), F(1), F(0)], [F(-4, 5), F(0), F(3, 5)]]
t = [F(1, 5), F(1, 10), F(2, 5)]
H = [[F(3, 5), F(0), F(9, 10)], [F(0), F(1), F(1, 20)], [F(-4, 5), F(0), F(4, 5)]]


def dot(x, y):
    return sum(a * b for a, b in zip(x, y, strict=True))


def mv(a, x):
    return [dot(row, x) for row in a]


def transpose(a):
    return list(map(list, zip(*a, strict=True)))


def mm(a, b):
    return [[dot(row, col) for col in transpose(b)] for row in a]


def det(a):
    return (
        a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
        - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
        + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
    )


def inv(a):
    b = [[F(int(i == j)) for j in range(3)] for i in range(3)]
    a = [row[:] for row in a]
    for i in range(3):
        k = next(k for k in range(i, 3) if a[k][i])
        a[i], a[k] = a[k], a[i]
        b[i], b[k] = b[k], b[i]
        c = a[i][i]
        a[i] = [x / c for x in a[i]]
        b[i] = [x / c for x in b[i]]
        for j in range(3):
            if j != i:
                c = a[j][i]
                a[j] = [x - c * y for x, y in zip(a[j], a[i], strict=True)]
                b[j] = [x - c * y for x, y in zip(b[j], b[i], strict=True)]
    return b


I = [[F(int(i == j)) for j in range(3)] for i in range(3)]
assert mm(transpose(R), R) == I and det(R) == 1
assert det(H) == F(6, 5)
G = inv(H)
assert mm(G, H) == I
corners = []
for u, v in product([F(-1, 2), F(1, 2)], [F(-1, 4), F(1, 4)]):
    p = [u, v, F(1)]
    X = [2 * z for z in p]
    Y = [a + b for a, b in zip(mv(R, X), t, strict=True)]
    q = mv(H, p)
    assert Y == [2 * z for z in q] and F(2, 5) <= q[2] <= F(6, 5)
    corners.append({"uv": [u, v], "q": q, "pixel": [q[0] / q[2], q[1] / q[2]], "depth2": Y[2]})
# Fixed line l: u=0. Incidence preserved, but normalized raw residual changes.
l = [F(1), F(0), F(0)]
ll = mv(transpose(G), l)
residuals = []
for u in [F(-1, 2), F(1, 2)]:
    p = [u, F(0), F(1)]
    q = mv(H, p)
    qh = [z / q[2] for z in q]
    assert dot(ll, q) == dot(l, p)
    transformed = dot(ll, qh)
    assert transformed == u / q[2]
    residuals.append(
        {"u": u, "source_residual": u, "target_normalized_residual": transformed, "height": q[2]}
    )
assert abs(residuals[0]["source_residual"]) == abs(residuals[1]["source_residual"])
assert abs(residuals[0]["target_normalized_residual"]) != abs(
    residuals[1]["target_normalized_residual"]
)
# Exact global patch denominator under independently bounded third-row perturbations.
eps = F(1, 1000)
perturbed = []
for u, v, e0, e1, e2 in product(
    [F(-1, 2), F(1, 2)], [F(-1, 4), F(1, 4)], [-eps, eps], [-eps, eps], [-eps, eps]
):
    perturbed.append((H[2][0] + e0) * u + (H[2][1] + e1) * v + H[2][2] + e2)
assert min(perturbed) == F(1593, 4000) > 0
# Negative projective matrix scale: same pixel, opposite raw height. Sign is not gauge invariant.
q = mv(H, [F(0), F(0), F(1)])
neg = [-z for z in q]
assert [q[i] / q[2] for i in range(2)] == [neg[i] / neg[2] for i in range(2)] and neg[2] < 0
out = {
    "R": R,
    "t": t,
    "plane": "Z=2",
    "H": H,
    "detH": det(H),
    "inverseH": G,
    "corners": corners,
    "line": l,
    "transformed_line": ll,
    "residuals": residuals,
    "third_row_error_each": eps,
    "perturbed_height_min": min(perturbed),
    "negative_scale_same_pixel": True,
    "scope": "Exact known-camera fixture and scalar perturbation box. Signed height uses canonical physical H gauge. No camera estimation, occlusion, pixel-noise or hardware guarantee.",
}
(P / "pm_patch.json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print(json.dumps(out, default=str))
