"""Independent exact rational check of plane transform and center-singularity criterion."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def mv(A, x):
    return [dot(r, x) for r in A]


def det(A):
    return (
        A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
        - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
        + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])
    )


rotations = [
    ("identity", [[1, 0, 0], [0, 1, 0], [0, 0, 1]]),
    ("proper_y_rotation", [[F(3, 5), 0, F(4, 5)], [0, 1, 0], [F(-4, 5), 0, F(3, 5)]]),
    ("nonrigid_affine_diagnostic", [[2, 0, 0], [0, 3, 0], [0, 0, 4]]),
]
rows = []
for (label, R), y, n, d in product(
    rotations,
    [[-1, 0, 0], [0, 0, 0], [1, 2, -1]],
    [[1, 0, 0], [0, 0, 1], [1, 2, 1]],
    [F(1), F(2), F(-1)],
):
    t = mv(R, y)
    H = [[F(R[i][j]) + t[i] * n[j] / d for j in range(3)] for i in range(3)]
    expected = det(R) * (1 + dot(n, y) / d)
    actual = det(H)
    assert expected == actual
    assert (actual == 0) == (dot(n, [-v for v in y]) == d)
    pivot = next(i for i in range(3) if n[i])
    X = [F(1), F(2), F(3)]
    X[pivot] = (d - sum(n[j] * X[j] for j in range(3) if j != pivot)) / n[pivot]
    assert dot(n, X) == d and mv(H, X) == [a + b for a, b in zip(mv(R, X), t, strict=True)]
    rows.append(
        {
            "R_kind": label,
            "y": y,
            "n": n,
            "d": str(d),
            "detH": str(actual),
            "center_on_plane": actual == 0,
        }
    )
result = {
    "checks": len(rows),
    "singular": sum(r["center_on_plane"] for r in rows),
    "scope": "Exact algebra, 2physical rotations and1explicit nonrigid diagnostic. No uniqueness, orientation, finite-image chart, or conditioning inference.",
    "rows": rows,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print({"checks": len(rows), "singular": result["singular"]})
