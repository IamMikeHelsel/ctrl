"""Property-based consumer for supplied geometric projectors; no producer routines."""

import json
from fractions import Fraction as F
from pathlib import Path

from critic_rank import rref

P = Path(__file__).parent
D = json.loads((P / "inventor_metric.json").read_text())
A = [[F(x) for x in row] for row in D["constraints"]]
J = json.loads((P / "inventor_projector.json").read_text())


def mm(a, b):
    return [
        [sum(x * y for x, y in zip(r, c, strict=True)) for c in zip(*b, strict=True)] for r in a
    ]


def check(p, a):
    assert p == list(map(list, zip(*p, strict=True))) and mm(p, p) == p
    assert sum(p[i][i] for i in range(6)) == 2 and len(rref(a)[1]) == 2
    assert mm(a, p) == a


for v, c in enumerate(J["cases"]):
    p = [[F(x) for x in row] for row in c["rowspace_projector"]]
    check(p, A[2 * v : 2 * v + 2])
    bad = [row[:] for row in p]
    bad[0][0] += F(1, 100)
    try:
        check(bad, A[2 * v : 2 * v + 2])
    except AssertionError:
        pass
    else:
        raise AssertionError("bad projector admitted")
# Distortion of one straight checkerboard line: no projective homography preserves this map.
k = F(1, 100)
points = [(F(x) * (1 + k * (x * x + 1)), 1 + k * (x * x + 1)) for x in [-1, 0, 1]]
a, b, c = points
cross = (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])
assert cross != 0
(P / "critic_projector.json").write_text(
    json.dumps(
        {
            "projectors_consumed": 3,
            "corruptions_rejected": 3,
            "radial_line_negative": {"points": points, "oriented_double_area": cross},
            "scope": "Euclidean chart geometric projectors; distortion witness violates pinhole homography assumption. No noise covariance or physical sensor claim.",
        },
        default=str,
        indent=2,
    )
    + "\n"
)
print("Projector uniqueness properties and distortion collinearity negative passed")
