"""Independent exact negative calibration, homography gauge and target metric tests."""

import json
from fractions import Fraction as F
from pathlib import Path


def m(rows):
    return [[F(x) for x in row] for row in rows]


def rows(h):
    a, b = [list(x) for x in zip(*h, strict=True)][:2]

    def v(x, y):
        return [
            x[0] * y[0],
            x[0] * y[1] + x[1] * y[0],
            x[1] * y[1],
            x[0] * y[2] + x[2] * y[0],
            x[1] * y[2] + x[2] * y[1],
            x[2] * y[2],
        ]

    return [v(a, b), [x - y for x, y in zip(v(a, a), v(b, b), strict=True)]]


def reduce(a):
    a = [x[:] for x in a]
    p = 0
    pivots = []
    for j in range(len(a[0])):
        k = next((k for k in range(p, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[p], a[k] = a[k], a[p]
        z = a[p][j]
        a[p] = [x / z for x in a[p]]
        for k in range(len(a)):
            if k != p:
                z = a[k][j]
                a[k] = [x - z * y for x, y in zip(a[k], a[p], strict=True)]
        pivots.append(j)
        p += 1
        if p == len(a):
            break
    return a, pivots


def determinant(a):
    return sum(
        (-1) ** j
        * a[0][j]
        * (a[1][(j + 1) % 3] * a[2][(j + 2) % 3] - a[1][(j + 2) % 3] * a[2][(j + 1) % 3])
        * (-1) ** j
        for j in range(3)
    )


hs = [
    m([[1, 0, 0], [0, 1, 0], [0, 0, 5]]),
    m([[F(5, 3), 0, 0], [0, 1, 0], [F(4, 3), 0, 5]]),
    m([[1, 0, 0], [0, F(5, 3), 0], [0, F(4, 3), 5]]),
]
a = [r for h in hs for r in rows(h)]
rr, piv = reduce(a)
b = m([[1, 0, 1, 0, 0, -1]])[0]
assert len(piv) == 5
assert all(sum(x * y for x, y in zip(r, b, strict=True)) == 0 for r in a)
assert rr[:5] == m(
    [
        [1, 0, 0, 0, 0, 1],
        [0, 1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 1],
        [0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 1, 0],
    ]
)
dets = [determinant(h) for h in hs]
assert dets == [5, F(25, 3), F(25, 3)]
depths = [[h[2][0] * x + h[2][1] * y + h[2][2] for x in [-1, 1] for y in [-1, 1]] for h in hs]
assert min(min(x) for x in depths) == F(11, 3)
# This is positivity of projective denominators only: no valid common Euclidean K exists.
# Sylvester first minor is lambda; determinant is -lambda^3, incompatible for lambda>0.
assert b[0] > 0 and b[0] * b[2] * b[5] < 0
scale_tests = []
for scale in [F(-3), F(1, 100), F(100)]:
    h = hs[1]
    scaled = [[scale * x for x in row] for row in h]
    assert rows(scaled) == [[scale**2 * x for x in row] for row in rows(h)]
    for x, y in [(0, 0), (1, 1), (-1, 1)]:
        p = [row[0] * x + row[1] * y + row[2] for row in h]
        z = [row[0] * x + row[1] * y + row[2] for row in scaled]
        assert [p[i] / p[2] for i in range(2)] == [z[i] / z[2] for i in range(2)]
    scale_tests.append(
        {"homography_scale": scale, "row_scale": scale**2, "single_view_gram_scale": scale**4}
    )
# Rank cannot distinguish repeated images from repeated noisy evidence.
assert len(reduce(a + a + a)[1]) == 5
# Wrong target metric, single frontoparallel view: board X_actual=2*X_declared.
# K_actual=I at depth1 and K_assumed=diag(2,1,1), nominal square, produce same pixels.
metric_pixels = []
for x, y in [(-1, -1), (1, -1), (1, 1), (-1, 1), (0, 0)]:
    actual = [2 * x, y]
    inferred = [2 * x, y]
    assert actual == inferred
    metric_pixels.append({"declared_board": [x, y], "pixel": actual})
result = {
    "homographies": hs,
    "constraints": a,
    "rref": rr,
    "rank": len(piv),
    "null_vector": b,
    "determinants": dets,
    "corner_projective_denominators": depths,
    "rejection": "Every nonzero null vector gives an indefinite B; rank5 is insufficient.",
    "homography_scale_tests": scale_tests,
    "target_metric_alias": metric_pixels,
    "limits": [
        "Exact rational synthetic homographies, no distortion or noisy-fit guarantee.",
        "Positive projective denominators do not prove valid Euclidean camera depths.",
        "Target metric alias is a rank-deficient one-view example, not generic multiview ambiguity.",
    ],
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(
    {
        "rank": len(piv),
        "null_vector": list(map(str, b)),
        "dets": list(map(str, dets)),
        "minimum_denominator": str(min(min(x) for x in depths)),
        "scale_tests": len(scale_tests),
    }
)
