"""Independent Gaussian-elimination reconstruction of exact support hypotheses."""

import json
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def mv(a, x):
    return tuple(dot(row, x) for row in a)


def columns(a):
    return tuple(zip(*a, strict=True))


def inverse(a):
    rows = [list(map(F, a[i])) + [F(i == j) for j in range(3)] for i in range(3)]
    for k in range(3):
        pivot = next((j for j in range(k, 3) if rows[j][k]), None)
        if pivot is None:
            return None
        rows[k], rows[pivot] = rows[pivot], rows[k]
        v = rows[k][k]
        rows[k] = [x / v for x in rows[k]]
        for i in range(3):
            if i != k:
                v = rows[i][k]
                rows[i] = [x - v * y for x, y in zip(rows[i], rows[k], strict=True)]
    return tuple(tuple(row[3:]) for row in rows)


def fits(X, Y, n):
    result = {}
    for ids in combinations(range(len(X)), 3):
        x0, x1, x2 = (X[i] for i in ids)
        y0, y1, y2 = (Y[i] for i in ids)
        u, v = sub(x1, x0), sub(x2, x0)
        uu, vv = sub(y1, y0), sub(y2, y0)
        if (dot(u, u), dot(v, v), dot(u, v)) != (dot(uu, uu), dot(vv, vv), dot(uu, vv)):
            continue
        source = columns((u, v, cross(u, v)))
        target = columns((uu, vv, cross(uu, vv)))
        inv = inverse(source)
        if inv is None:
            continue
        R = tuple(tuple(dot(row, col) for col in columns(inv)) for row in target)
        assert all(
            dot(a, b) == (i == j)
            for i, a in enumerate(columns(R))
            for j, b in enumerate(columns(R))
        )
        assert dot(R[0], cross(R[1], R[2])) == 1
        t = sub(y0, mv(R, x0))
        support = tuple(
            i for i, (x, y) in enumerate(zip(X, Y, strict=True)) if sub(y, mv(R, x)) == t
        )
        if len(support) >= n:
            result[(R, t)] = support
    return result


X = [(F(0),) * 3, (F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1))]
Y = X[:3] + [(F(0), F(0), F(-1))]
four = fits(X, Y, 3)
off = (F(0), F(2), F(1))
on = (F(2), F(0), F(0))
five = fits(X + [off], Y + [off], 4)
axis = fits(X + [on], Y + [on], 4)
assert [len(four), len(five), len(axis)] == [4, 1, 2]
saved = json.loads((HERE / "inventor_support.json").read_text())
for field, actual in [
    ("four_pair_all_three_point_fits", four),
    ("off_axis_fifth_pair_four_point_fits", five),
    ("on_axis_fifth_pair_negative", axis),
]:
    recovered = {}
    for r in saved[field]:
        R = columns(tuple(tuple(F(v) for v in c) for c in r["rotation_columns"]))
        t = tuple(F(v) for v in r["translation"])
        recovered[(R, t)] = tuple(r["support"])
    assert recovered == actual
tetra = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
unlabeled = {}
for perm in permutations(range(4)):
    unlabeled.update(fits(tetra, [tetra[i] for i in perm], 4))
assert len(fits(tetra, tetra, 4)) == 1 and len(unlabeled) == 12
scores = {}
for p in product(range(-2, 3), repeat=3):
    if dot(p, p) > 5:
        continue
    predictions = [tuple(a + b for a, b in zip(mv(R, p), t, strict=True)) for R, t in four]
    scores[p] = min(dot(sub(a, b), sub(a, b)) for a, b in combinations(predictions, 2))
assert len(scores) == 57 and max(scores.values()) == 8
assert scores[(-1, -1, -1)] == 8 and scores[off] == 4
record = saved["finite_virtual_query_pool"]
assert record["count"] == len(scores) and F(record["best_minimum_gap_squared"]) == 8
assert {tuple(F(v) for v in p) for p in record["maximizers"]} == {
    p for p, s in scores.items() if s == 8
}
reflection = ((F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(-1)))
assert [
    i for i, (p, q) in enumerate(zip(X + [off], Y + [off], strict=True)) if mv(reflection, p) == q
] == [0, 1, 2, 3]
assert dot(reflection[0], cross(reflection[1], reflection[2])) == -1
readout = (F(0), F(2), F(0))
initial_predictions = [tuple(a + b for a, b in zip(mv(R, off), t, strict=True)) for R, t in four]
assert sum(dot(sub(pred, readout), sub(pred, readout)) <= 1 for pred in initial_predictions) == 2
assert scores[(-1, -1, -1)] > 4  # All four closed radius1 observation balls disjoint.
result = {
    "exact_support_fit_counts": [4, 1, 2],
    "regular_tetra_fixed_vs_unlabeled": [1, 12],
    "active_query_count": 57,
    "active_maximin_squared": 8,
    "initial_offaxis_squared": 4,
    "best_points": [p for p, s in scores.items() if s == 8],
    "fifth_point_O3_alternative_verified": True,
    "original_query_readout_radius1_compatible_models": 2,
    "best_query_all_radius1_balls_pairwise_disjoint": True,
    "method": "Own rational Gaussian elimination and full triple/permutation enumeration; serialized producer poses matched exactly.",
    "scope": "Zero-noise exact support completeness relies on every retained support containing a noncollinear triple. Active query scores only this complete finite exact-model list, not noisy pose branches or physical acquisition feasibility.",
}
(HERE / "critic_support.json").write_text(json.dumps(result, indent=2) + "\n")
print(result)
