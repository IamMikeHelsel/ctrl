"""Independent rational geometry of the actual source ellipsoid."""

import json
from fractions import Fraction as F
from pathlib import Path

P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]
k = [F(-1), F(-3), F(-2)]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def mv(M, z):
    return [dot(r, z) for r in M]


def energy(z):
    return dot(z, mv(P, z))


def solve(M, b):
    a = [r[:] + [x] for r, x in zip(M, b, strict=True)]
    for j in range(len(b)):
        pivot = next(i for i in range(j, len(b)) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        d = a[j][j]
        a[j] = [x / d for x in a[j]]
        for i in range(len(b)):
            if i != j:
                d = a[i][j]
                a[i] = [x - d * y for x, y in zip(a[i], a[j], strict=True)]
    return [r[-1] for r in a]


y = solve(P, k)
g = dot(k, y)
threshold = 1 / g
assert mv(P, y) == k
# Every u-fixed affine slice minimizes energy at z=(u/g)P^-1 k.
z1 = [x / g for x in y]
assert dot(k, z1) == 1 and energy(z1) == threshold
z2 = [2 * x for x in z1]
assert dot(k, z2) == 2 and energy(z2) < 12
# Exact square completion for representative directions; general identity polynomial.
for z in [
    [F(a, 3), F(b, 5), F(c, 7)] for a in range(-2, 3) for b in range(-2, 3) for c in range(-2, 3)
]:
    u = dot(k, z)
    r = [zi - u * yi / g for zi, yi in zip(z, y, strict=True)]
    assert energy(z) == u * u / g + energy(r)
# Independent LDL cert for source positive definiteness.
L = [[F(int(i == j)) for j in range(3)] for i in range(3)]
D = []
for j in range(3):
    D.append(P[j][j] - sum(L[j][s] ** 2 * D[s] for s in range(j)))
    for i in range(j + 1, 3):
        L[i][j] = (P[i][j] - sum(L[i][s] * L[j][s] * D[s] for s in range(j))) / D[j]
assert all(d > 0 for d in D)
assert all(
    sum(L[i][s] * D[s] * L[j][s] for s in range(3)) == P[i][j] for i in range(3) for j in range(3)
)
assert energy([F(0), F(0), F(1)]) == F(278, 25) < 12
assert energy([F(0)] * 3) == 0 and dot(k, [F(0)] * 3) == 0
out = {
    "P": [[str(x) for x in r] for r in P],
    "control": list(map(str, k)),
    "P_inverse_k": list(map(str, y)),
    "dual_norm_squared": str(g),
    "energy_at_activation_boundary": str(threshold),
    "energy_for_request2": str(4 * threshold),
    "request2_state": list(map(str, z2)),
    "max_request_squared_at_R12": str(12 * g),
    "LDL_positive": list(map(str, D)),
    "scope": "Threshold and complete square identity are exact rational hand algebra with finite checker. Strict active clipping iff R>threshold; origin refutes everywhere-active interpretation.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
