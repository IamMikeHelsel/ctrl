"""Exact calibration rank, metric-signature, scale and depth controls."""

import json
from fractions import Fraction as F
from pathlib import Path


def ij(x, y):
    return [
        x[0] * y[0],
        x[0] * y[1] + x[1] * y[0],
        x[1] * y[1],
        x[2] * y[0] + x[0] * y[2],
        x[2] * y[1] + x[1] * y[2],
        x[2] * y[2],
    ]


def rows(H):
    a = [r[0] for r in H]
    b = [r[1] for r in H]
    return [ij(a, b), [x - y for x, y in zip(ij(a, a), ij(b, b), strict=True)]]


def rref(a):
    a = [[F(x) for x in r] for r in a]
    piv = []
    i = 0
    for j in range(6):
        k = next((k for k in range(i, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[i], a[k] = a[k], a[i]
        d = a[i][j]
        a[i] = [x / d for x in a[i]]
        for k in range(len(a)):
            if k != i:
                d = a[k][j]
                a[k] = [x - d * y for x, y in zip(a[k], a[i], strict=True)]
        piv.append(j)
        i += 1
        if i == len(a):
            break
    return a, piv


def design(views):
    return [r for H in views for r in rows(H)]


def det(H):
    return (
        H[0][0] * (H[1][1] * H[2][2] - H[1][2] * H[2][1])
        - H[0][1] * (H[1][0] * H[2][2] - H[1][2] * H[2][0])
        + H[0][2] * (H[1][0] * H[2][1] - H[1][1] * H[2][0])
    )


H0 = [[F(1), 0, 0], [0, F(1), 0], [0, 0, F(5)]]
Hx = [[F(5, 3), 0, 0], [0, F(1), 0], [F(4, 3), 0, F(5)]]
Hy = [[F(1), 0, 0], [0, F(5, 3), 0], [0, F(4, 3), F(5)]]
bad = [H0, Hx, Hy]
B = [F(1), 0, F(1), 0, 0, F(-1)]
M = design(bad)
RR, piv = rref(M)
assert len(piv) == 5 and all(sum(x * y for x, y in zip(r, B, strict=True)) == 0 for r in M)
assert all(
    det(H) != 0 and min(H[2][0] * x + H[2][1] * y + H[2][2] for x in [-1, 1] for y in [-1, 1]) > 0
    for H in bad
)
# Nullspace is exactly diag(1,1,-1) up to nonzero scale; either sign indefinite.
assert RR[:5] == [
    [F(1), 0, 0, 0, 0, F(1)],
    [0, F(1), 0, 0, 0, 0],
    [0, 0, F(1), 0, 0, F(1)],
    [0, 0, 0, F(1), 0, 0],
    [0, 0, 0, 0, F(1), 0],
]
c, s = F(3, 5), F(4, 5)
Rx = [[F(1), 0, 0], [0, c, 0], [0, s, F(5)]]
Ry = [[c, 0, 0], [0, F(1), 0], [-s, 0, F(5)]]
Rz = [[c, -s, 0], [s, c, 0], [0, 0, F(5)]]
good = [H0, Rx, Ry]
G = design(good)
GI = [F(1), 0, F(1), 0, 0, F(1)]
assert len(rref(G)[1]) == 5 and all(sum(x * y for x, y in zip(r, GI, strict=True)) == 0 for r in G)
assert len(rref(design([H0, Rz, H0]))[1]) == 2
assert len(rref(design([Rx, Ry]))[1]) == 4
assert len(rref(design([Rx, Ry]) + [[0, 1, 0, 0, 0, 0]])[1]) == 5
# Independent homography scale multiplies each two-row block by scale^2.
scales = [F(1, 1000), F(-7), F(13, 5)]
scaled = [[[a * x for x in row] for row in H] for a, H in zip(scales, good, strict=True)]
assert len(rref(design(scaled))[1]) == 5
for i, a in enumerate(scales):
    assert rows(scaled[i]) == [[a * a * x for x in row] for row in rows(good[i])]
# h3 is absent from intrinsic equations: a board can straddle depth0 despite rank5+SPD.
straddling = [[row[:] for row in H] for H in good]
straddling[2][2][2] = F(1, 10)
assert design(straddling) == G and det(straddling[2]) != 0
assert straddling[2][2][0] + straddling[2][2][2] == F(-7, 10)
assert -straddling[2][2][0] + straddling[2][2][2] == F(9, 10)
out = {
    "indefinite": {
        "homographies": bad,
        "design": M,
        "rref": RR,
        "rank": 5,
        "kernel": B,
        "positive_projective_depth_on_board": True,
        "not_a_common_intrinsic_camera": "Every nonzero metric on kernel line is indefinite",
    },
    "positive_ranks": {
        "three_tilts": 5,
        "parallel_spin_repeats": 2,
        "two_views": 4,
        "two_plus_zero_skew": 5,
    },
    "homography_scale_rule": "constraintblock scales bys^2; exactrank unchanged but raw singularvalues/weights change",
    "cheirality_negative": {
        "same_design_rank": 5,
        "same_SPD_kernel": True,
        "depths": ["-7/10", "9/10"],
    },
    "scope": "Exact rational synthetic fixtures; no checkerboard extraction, noise robustness, distortion or realcamera claim.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print("Rank5 indefinite counterexample, scale controls and cheirality negative passed")
