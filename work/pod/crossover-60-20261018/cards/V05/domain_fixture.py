"""Exact squared-distance and two-pose checks, no registration solver."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

A = [(0, 0, 0), (1, 0, 0), (0, 1, 0)]
B = [(0, 0, 1), (1, 0, 1), (0, 1, 1)]
D = (10, 0, 0)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b, strict=True))


def sqdist(a, b):
    return sum((F(x) - F(y)) ** 2 for x, y in zip(a, b, strict=True))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


src = A + B
tgt = A + [add(x, D) for x in B]
assert len(set(src)) == len(set(tgt)) == 6
assert cross(sub(A[1], A[0]), sub(A[2], A[0])) != (0, 0, 0)
assert cross(sub(B[1], B[0]), sub(B[2], B[0])) != (0, 0, 0)
checks = []
for i, j in product(range(3), repeat=2):
    ds = sqdist(A[i], B[j])
    dt = sqdist(A[i], add(B[j], D))
    assert ds <= 4 and dt >= 81
    checks.append({"i": i, "j": j, "source_squared": str(ds), "target_squared": str(dt)})
poses = []
for t in [(0, 0, 0), D]:
    residuals = [sqdist(add(x, t), y) for x, y in zip(src, tgt, strict=True)]
    tls = sum(min(r, F(1)) for r in residuals)
    assert tls == 3
    poses.append(
        {
            "rotation": "identity determinant+1",
            "scale": 1,
            "translation": t,
            "squared_residuals": list(map(str, residuals)),
            "tls": str(tls),
        }
    )
result = {
    "sources": src,
    "targets": tgt,
    "cross_checks": checks,
    "poses": poses,
    "scope": "Fixed labelled correspondences; known scale1; exact Euclidean TLS cap1. "
    "Lower bound over continuous isometries is separately proved in Lean.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(
    "PASS: 9 exact cross-distance bounds, 2 attaining proper rigid poses, distinct noncollinear groups"
)
