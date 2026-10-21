"""Exact fixture checks and continuous-pose certificate premises, no solver calls."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
A = [(F(0), F(0), F(0)), (F(1), F(0), F(0)), (F(0), F(1), F(0))]
B = [(x, y, z + 1) for x, y, z in A]
X = A + B
Y = A + [(x + 10, y, z) for x, y, z in B]
I = ((F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1)))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


def norm2(a):
    return sum(x * x for x in a)


def mv(R, x):
    return tuple(sum(a * b for a, b in zip(row, x, strict=True)) for row in R)


def det(R):
    return (
        R[0][0] * (R[1][1] * R[2][2] - R[1][2] * R[2][1])
        - R[0][1] * (R[1][0] * R[2][2] - R[1][2] * R[2][0])
        + R[0][2] * (R[1][0] * R[2][1] - R[1][1] * R[2][0])
    )


def proper(R):
    return det(R) == 1 and all(
        sum(R[k][i] * R[k][j] for k in range(3)) == (i == j) for i in range(3) for j in range(3)
    )


def residuals(R, t, scale=F(1), source=X, target=Y):
    return [
        norm2(tuple(scale * v + t[i] - y[i] for i, v in enumerate(mv(R, x))))
        for x, y in zip(source, target, strict=True)
    ]


assert proper(I)
cross = []
for i in range(3):
    for j in range(3, 6):
        dx2, dy2 = norm2(sub(X[i], X[j])), norm2(sub(Y[i], Y[j]))
        assert dx2 <= 3 < F(49, 16)
        assert dy2 >= 81
        cross.append([i, j, str(dx2), str(dy2)])
# Every cross pair has distance gap>2 at scale1, so no two residuals<1
# can occupy different groups. This uses distance preservation for all O(3),
# and therefore all SO(3), not enumeration of candidate poses.
for group in (range(3), range(3, 6)):
    for i, j in combinations(group, 2):
        dx2, dy2 = norm2(sub(X[i], X[j])), norm2(sub(Y[i], Y[j]))
        assert 1 <= dx2 and dy2 < 4
# All positive scales: s<=4 implies scaled cross-distance<7 vs target>=9;
# s>4 implies within-group scaled distance>4 vs target<2.
fits = []
for t in ((F(0), F(0), F(0)), (F(10), F(0), F(0))):
    rr = residuals(I, t)
    cost = sum(min(F(1), e) for e in rr)
    assert cost == 3
    fits.append(
        {
            "translation": list(map(str, t)),
            "squared_residuals": list(map(str, rr)),
            "TLS": str(cost),
        }
    )
# Three noncollinear pairs are required for a proper rigid uniqueness bridge.
rx = ((F(1), F(0), F(0)), (F(0), F(0), F(-1)), (F(0), F(1), F(0)))
line = [(F(i), F(0), F(0)) for i in range(3)]
assert proper(rx) and rx != I
assert all(e == 0 for e in residuals(rx, (F(0),) * 3, source=line, target=line))
# A full distance clique does not enforce SO(3) chirality.
tetra = [(F(0),) * 3] + [tuple(F(i == j) for i in range(3)) for j in range(3)]
reflection = ((F(-1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1)))
mirrored = [mv(reflection, x) for x in tetra]
assert det(reflection) == -1 and not proper(reflection)
assert all(
    norm2(sub(tetra[i], tetra[j])) == norm2(sub(mirrored[i], mirrored[j]))
    for i, j in combinations(range(4), 2)
)
# Fixed source0,e1,e2,e3 forces columns of any exact affine fit to this reflection.
scaled = [tuple(2 * v for v in x) for x in tetra]
assert all(e == 0 for e in residuals(I, (F(0),) * 3, scale=F(2), source=tetra, target=scaled))
assert not proper(tuple(tuple(2 * v for v in row) for row in I))
result = {
    "sources": [[str(v) for v in x] for x in X],
    "targets": [[str(v) for v in y] for y in Y],
    "cross_pair_squared_distances": cross,
    "attaining_SO3_fits": fits,
    "continuous_lower_bound": 3,
    "unknown_positive_scale_bound": "Same lower3; split s<=4 cross incompatibility, s>4 within-group incompatibility. Attainment forces3 zero residuals in one group, hence s1.",
    "negative_controls": [
        "collinear support admits distinct proper rotations",
        "reflected tetrahedron preserves every pairdistance but has no exact proper rigid fit",
        "2I fits scaled tetrahedron but is not a rotation",
    ],
    "scope": "Exact rational premises plus explicit triangle-inequality hand derivation. No TEASER implementation run, no novelty or correspondence-search guarantee.",
}
(HERE / "critic_fixture.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            k: v
            for k, v in result.items()
            if k not in ("sources", "targets", "cross_pair_squared_distances")
        },
        indent=2,
    )
)
