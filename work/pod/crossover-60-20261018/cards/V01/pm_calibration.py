"""Independent rational calibration conjugation fixture, no pixel measurements."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

P = Path(__file__).resolve().parent
H = [[F(3, 5), 0, F(9, 10)], [0, 1, F(1, 20)], [F(-4, 5), 0, F(4, 5)]]
K1 = [[800, 0, 320], [0, 1000, 240], [0, 0, 1]]
G1 = [[F(1, 800), 0, F(-2, 5)], [0, F(1, 1000), F(-6, 25)], [0, 0, 1]]
K2 = [[900, 50, 300], [0, 1100, 200], [0, 0, 1]]


def mv(a, x):
    return [sum(F(ai) * xi for ai, xi in zip(row, x, strict=True)) for row in a]


def mm(a, b):
    return [[sum(F(a[i][k]) * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def norm(p):
    assert p[2] != 0
    return [p[0] / p[2], p[1] / p[2], F(1)]


assert mm(G1, K1) == [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
Hp = mm(mm(K2, H), G1)
rows = []
for u, v in product([F(-1, 2), F(0), F(1, 2)], [F(-1, 4), F(0), F(1, 4)]):
    ray = [u, v, F(1)]
    pix1 = mv(K1, ray)
    q = mv(H, ray)
    pix2 = norm(mv(K2, q))
    via = norm(mv(Hp, pix1))
    wrong = norm(mv(H, pix1))
    assert via == pix2 and wrong != pix2
    rows.append({"ray": ray, "pixel1": pix1, "pixel2": pix2, "wrong_uncalibrated": wrong})
assert rows[4]["pixel2"] == [F(10525, 8), F(1075, 4), F(1)]
out = {
    "K1": K1,
    "K1inv": G1,
    "K2": K2,
    "pixel_homography": Hp,
    "nine_exact_correspondences": rows,
    "scope": "Synthetic exact known-calibration conjugation. Forgetting calibration changes the mapping; this does not claim source bug, estimated calibration fidelity, physical observability or robustness to pixel noise.",
}
(P / "pm_calibration.json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print(
    json.dumps(
        {"cases": len(rows), "central_target": rows[4]["pixel2"], "pixel_homography": Hp},
        default=str,
    )
)
