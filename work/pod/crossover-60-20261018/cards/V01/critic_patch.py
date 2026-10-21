"""Independent exact consumer of PM patch/calibration receipts."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

P = Path(__file__).resolve().parent


def dot(a, b):
    return sum((x * y for x, y in zip(a, b, strict=True)), F(0))


def mv(a, x):
    return [dot(r, x) for r in a]


def trans(a):
    return list(map(list, zip(*a, strict=True)))


def mm(a, b):
    return [[dot(r, c) for c in trans(b)] for r in a]


def parse(a):
    return [[F(x) for x in r] for r in a]


def norm(p):
    assert p[2] != 0
    return [v / p[2] for v in p]


def identity():
    return [[F(i == j) for j in range(3)] for i in range(3)]


p = json.loads((P / "pm_patch.json").read_text())
H, R, G = (parse(p[k]) for k in ["H", "R", "inverseH"])
t = list(map(F, p["t"]))
assert mm(trans(R), R) == identity() and mm(G, H) == identity()
assert H == [[R[i][j] + (t[i] / 2 if j == 2 else 0) for j in range(3)] for i in range(3)]
l = mv(trans(G), [F(1), F(0), F(0)])
assert l == [F(2, 3), 0, F(-3, 4)]
checks = 0
for u, v in product([F(i, 20) for i in range(-10, 11)], [F(j, 20) for j in range(-5, 6)]):
    x = [u, v, F(1)]
    y = mv(H, x)
    assert [2 * q for q in y] == [a + b for a, b in zip(mv(R, [2 * q for q in x]), t, strict=True)]
    assert F(2, 5) <= y[2] <= F(6, 5)
    assert dot(l, norm(y)) == u / y[2]
    for tau in [F(0), F(1, 4), F(1, 2)]:
        assert (abs(dot(l, norm(y))) <= tau / y[2]) == (abs(u) <= tau)
    checks += 1
perturb = []
for u, v, a, b, c in product(
    [F(-1, 2), F(1, 2)],
    [F(-1, 4), F(1, 4)],
    [-F(1, 1000), F(1, 1000)],
    [-F(1, 1000), F(1, 1000)],
    [-F(1, 1000), F(1, 1000)],
):
    perturb.append((H[2][0] + a) * u + (H[2][1] + b) * v + H[2][2] + c)
assert min(perturb) == F(1593, 4000) == F(p["perturbed_height_min"])
# Wrong inverse direction and fixed raw threshold must be rejected.
y = mv(H, [F(0), F(0), F(1)])
assert dot(mv(H, [F(1), F(0), F(0)]), y) != 0
assert abs(dot(l, norm(mv(H, [F(1, 2), F(0), F(1)])))) > F(1, 2)
# Negative H gauge leaves pixel, but invalidates positivity-based threshold tau/q.
assert norm([-a for a in y]) == norm(y) and -y[2] < 0
# A third-row error bound alone does not bound pixel numerator error.
Hhuge = [r[:] for r in H]
Hhuge[0][2] += 100
assert mv(Hhuge, [0, 0, 1])[2] == y[2] and abs(norm(mv(Hhuge, [0, 0, 1]))[0] - norm(y)[0]) > 100
c = json.loads((P / "pm_calibration.json").read_text())
K1, K2, K1inv, Hp = (parse(c[k]) for k in ["K1", "K2", "K1inv", "pixel_homography"])
assert mm(K1inv, K1) == identity() and Hp == mm(mm(K2, H), K1inv)
for row in c["nine_exact_correspondences"]:
    ray = list(map(F, row["ray"]))
    pix = mv(K1, ray)
    assert norm(mv(Hp, pix)) == norm(mv(K2, mv(H, ray))) == list(map(F, row["pixel2"]))
    assert norm(mv(H, pix)) != list(map(F, row["pixel2"]))
out = {
    "patch_grid_exact_checks": checks,
    "vertex_denominator_min": str(min(perturb)),
    "calibration_checks": 9,
    "semantic_negatives": [
        "wrong line rule",
        "unscaled residual threshold",
        "negative H gauge",
        "denominator-only pixel error overclaim",
        "omitted calibration",
    ],
    "scope": "Independent rational receipt reconstruction plus finite grid; all-patch bound requires affine extremum or kernel theorem. Perturbed third row certifies visibility margin only, not complete perturbed point/line correctness.",
}
(P / "critic_patch.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
