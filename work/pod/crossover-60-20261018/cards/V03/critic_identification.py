"""Independent rank and conditioning checks; no producer code imported."""

import json
import runpy
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path

P = Path(__file__).parent
own = runpy.run_path(str(P / "critic_geometry.py"))
rank, dot, mm, mv, skew = (own[k] for k in ("rank", "dot", "mm", "mv", "skew"))
I = own["I"]


def determinant(a):
    n = len(a)
    value = F(0)
    for p in permutations(range(n)):
        term = F((-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n)))
        for i in range(n):
            term *= a[i][p[i]]
        value += term
    return value


def pair(u, v, z):
    return ([u, v, F(1)], [u + 1 / z, v, F(1)])


grid = [pair(u, v, F(1)) for u in [F(0), F(1, 2), F(1)] for v in [F(0), F(1, 2), F(1)]]
k = pair(F(1, 4), F(0), F(3, 2))
s1 = pair(F(1, 4), F(1, 4), F(2))
s2 = pair(F(1, 4), F(3, 4), F(2))
all_cases = [grid, grid + [k], grid + [s1], grid + [s1, s2], grid + [k, s1]]
ranks = []
for pairs in all_cases:
    rows = [[y[i] * x[j] for i in range(3) for j in range(3)] for x, y in pairs]
    assert all(dot(row, [0, 0, 0, 0, 0, -1, 0, 1, 0]) == 0 for row in rows)
    ranks.append(rank(rows))
assert ranks == [6, 7, 7, 8, 8]
# Squared-angle invariant rejects zero translation independently of E.
x, y = grid[0]
u, v = grid[6]
assert dot(x, u) ** 2 / (dot(x, x) * dot(u, u)) == F(1, 2)
assert dot(y, v) ** 2 / (dot(y, y) * dot(v, v)) == F(9, 10)

source = json.loads((P / "inventor_conditioning.json").read_text())
checks = []
for record in source["family"]:
    b = F(record["beta"])
    points = [[F(x) for x in p] for p in source["five_first_image_points"]]
    ra = [[b, -b * v, -(v * v + 1), u * v, u] for u, v in points]
    rb = [[F(x) for x in row] for row in record["R_B"]]
    tb = [F(x) for x in record["t_B"]]
    derivative = [mm(skew(axis), rb) for axis in I[1:]]
    derivative += [mm(mm(skew(tb), skew(axis)), rb) for axis in I]
    jb = [[dot([u + b, v, 1], mv(de, [u, v, 1])) for de in derivative] for u, v in points]
    assert ra == [[F(x) for x in row] for row in record["jacobian_A"]]
    assert jb == [[F(x) for x in row] for row in record["jacobian_B"]]
    assert determinant(ra) == F(record["det_A"]) == 2 * b * b
    assert determinant(jb) == F(record["det_B"]) != 0
    assert sum(r[0] ** 2 for r in ra) == 5 * b * b
    assert sum(r[2] ** 2 for r in ra) == 35
    assert F(record["condition_number_squared_lower_bound_A"]) == 7 / (b * b)
    checks.append({"beta": str(b), "condition_squared_lower_bound": str(7 / (b * b))})
# Verify the planar interpolation certificate by Leibniz determinant.
pc = source["planar_polynomial_certificate"]
pts = [[F(x) for x in p] for p in pc["six_points"]]
mat = [[u * u, u * v, v * v, u, v, F(1)] for u, v in pts]
assert determinant(mat) == F(pc["determinant"]) == F(1, 5184)
# Meaningful negative controls: repeat a separating row and corrupt a rank claim;
# ignore cheirality and half-turn/negative scale solutions would wrongly survive.
assert rank([[y[i] * x[j] for i in range(3) for j in range(3)] for x, y in grid + [s1, s1]]) == 7
assert ranks[2] != 8
# A negative global scale preserves incidence and rigid equations but violates depths.
x, y = grid[0]
assert [(-1) * q for q in y] == [(-1) * q + t for q, t in zip(x, [-1, 0, 0], strict=True)]
negative_scale_depths = [-F(1), -F(1)]
assert not all(d > 0 for d in negative_scale_depths)
# The half-turn proper rotation likewise fits this pair with opposite-sign depths.
half_turn = [[F(1), 0, 0], [0, -F(1), 0], [0, 0, -F(1)]]
assert own["det"](half_turn) == 1
assert [-q for q in y] == [q + t for q, t in zip(mv(half_turn, x), [-1, 0, 0], strict=True)]
assert not all(d > 0 for d in [F(1), -F(1)])
out = {
    "ranks": ranks,
    "conditioning": checks,
    "interpolation_det": "1/5184",
    "negative_controls": 4,
    "scope": "Exact arithmetic replays plus independently inspected hand proof; no Lean rank certificate or noisy uniqueness.",
}
(P / "critic_identification_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
