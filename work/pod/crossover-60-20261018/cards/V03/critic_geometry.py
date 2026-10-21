"""Independent rational rigid-pose and epipolar counterexample checks."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

BASE = Path(__file__).parent
I = [[F(i == j) for j in range(3)] for i in range(3)]
R = [[F(3, 5), 0, F(4, 5)], [0, 1, 0], [F(-4, 5), 0, F(3, 5)]]
tA = [F(1), F(0), F(0)]
tB = [F(1, 5), F(0), F(2, 5)]
H = [[1, 0, 1], [0, 1, 0], [0, 0, 1]]


def dot(a, b):
    return sum((x * y for x, y in zip(a, b, strict=True)), F(0))


def transpose(a):
    return list(map(list, zip(*a, strict=True)))


def mm(a, b):
    return [[dot(row, col) for col in transpose(b)] for row in a]


def mv(a, x):
    return [dot(row, x) for row in a]


def plus(a, b):
    return [[x + y for x, y in zip(ar, br, strict=True)] for ar, br in zip(a, b, strict=True)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def skew(t):
    x, y, z = t
    return [[0, -z, y], [z, 0, -x], [-y, x, 0]]


def det(a):
    return sum(
        (
            (-1) ** j
            * a[0][j]
            * (a[1][(j + 1) % 3] * a[2][(j + 2) % 3] - a[1][(j + 2) % 3] * a[2][(j + 1) % 3])
            * (-1) ** j
            for j in range(3)
        ),
        F(0),
    )


def rank(a):
    a = [list(map(F, row)) for row in a]
    pivot = 0
    for col in range(len(a[0])):
        chosen = next((r for r in range(pivot, len(a)) if a[r][col]), None)
        if chosen is None:
            continue
        a[pivot], a[chosen] = a[chosen], a[pivot]
        value = a[pivot][col]
        a[pivot] = [x / value for x in a[pivot]]
        for r in range(len(a)):
            if r != pivot:
                value = a[r][col]
                a[r] = [x - value * y for x, y in zip(a[r], a[pivot], strict=True)]
        pivot += 1
        if pivot == len(a):
            break
    return pivot


def essential_cubic(e):
    eet = mm(e, transpose(e))
    trace = sum(eet[i][i] for i in range(3))
    return plus(scale(2, mm(eet, e)), scale(-trace, e))


EA = mm(skew(tA), I)
EB = mm(skew(tB), R)
if mm(transpose(R), R) != I or det(R) != 1 or rank(EA) != 2 or rank(EB) != 2:
    raise ValueError("proper rigid pose or essential rank")
if any(any(row) for row in essential_cubic(EA)) or any(any(row) for row in essential_cubic(EB)):
    raise ValueError("calibrated essential cubic")
if rank([sum(EA, []), sum(EB, [])]) != 2:
    raise ValueError("essential matrices projectively equal")
if plus(R, [[a * b for b in [2, 0, 1]] for a in tB]) != H:
    raise ValueError("homography identity")
rows = []
witnesses = []
for u, v in product([F(0), F(1, 4), F(1, 2)], [F(-1, 4), F(0), F(1, 4)]):
    ray1 = [u, v, F(1)]
    ray2 = [u + 1, v, F(1)]
    depth = 1 / (2 * u + 1)
    X = [depth * z for z in ray1]
    transformed = [a + b for a, b in zip(mv(R, X), tB, strict=True)]
    if depth <= 0 or transformed != [depth * z for z in ray2] or dot([2, 0, 1], X) != 1:
        raise ValueError("positive-depth pose reconstruction")
    if dot(ray2, mv(EA, ray1)) or dot(ray2, mv(EB, ray1)):
        raise ValueError("epipolar correspondence")
    rows.append([a * b for a in ray2 for b in ray1])
    witnesses.append(dict(ray1=ray1, ray2=ray2, depth_A=1, depth_B=depth))
# Off-plane feature in actual pose A: X=(0,1,2), normalized second ray(.5,.5,1).
x = [F(0), F(1, 2), F(1)]
y = [F(1, 2), F(1, 2), F(1)]
offplaneA = dot(y, mv(EA, x))
offplaneB = dot(y, mv(EB, x))
if offplaneA or offplaneB != F(1, 10):
    raise ValueError("off-plane discriminating feature")
# Arbitrary-R algebraic object can have rank2 and fail calibrated essential cubic.
invalidR = [[1, 0, 0], [0, 2, 0], [0, 0, 3]]
invalidE = mm(skew(tA), invalidR)
if rank(invalidE) != 2 or not any(any(row) for row in essential_cubic(invalidE)):
    raise ValueError("nonrigid algebraic counterexample")
# Proper pose with plane through camera2 gives singular induced H; d!=0 alone insufficient.
singular = plus(I, [[a * b for b in [0, 0, 1]] for a in [0, 0, -1]])
if det(singular) != 0:
    raise ValueError("singular plane-homography counterexample")
result = dict(
    rotation_B=R,
    translation_A=tA,
    translation_B=tB,
    EA=EA,
    EB=EB,
    essential_design_rank=rank(rows),
    positive_depth_correspondences=witnesses,
    offplane_residuals=[offplaneA, offplaneB],
    rank2_nonessential=invalidE,
    nonessential_cubic=essential_cubic(invalidE),
    singular_H=singular,
    scope="Exact rational pose ambiguity with positive depths; not a generic uniqueness theorem. E scale is arbitrary; raw residual1/10 is gauge-specific.",
)
(BASE / "critic_geometry_results.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(
    json.dumps(
        {k: v for k, v in result.items() if k != "positive_depth_correspondences"},
        default=str,
        indent=2,
    )
)
