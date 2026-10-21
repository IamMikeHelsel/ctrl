"""Exact SO(2) cycle primal/dual certificate, independent of any optimizer."""

import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent


def rot(c, s):
    return [[Q(c), -Q(s)], [Q(s), Q(c)]]


def tr(a):
    return [list(x) for x in zip(*a, strict=True)]


def mul(a, b):
    return [[sum(x * y for x, y in zip(row, col, strict=True)) for col in tr(b)] for row in a]


def ident(n):
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def encode(a):
    if isinstance(a, list):
        return [encode(x) for x in a]
    return str(a)


def ldl(a):
    n = len(a)
    low, d = ident(n), [Q(0)] * n
    for j in range(n):
        d[j] = a[j][j] - sum(low[j][k] ** 2 * d[k] for k in range(j))
        assert d[j] >= 0
        for i in range(j + 1, n):
            v = a[i][j] - sum(low[i][k] * low[j][k] * d[k] for k in range(j))
            if d[j] == 0:
                assert v == 0
            else:
                low[i][j] = v / d[j]
    assert (
        mul(mul(low, [[d[i] if i == j else Q(0) for j in range(n)] for i in range(n)]), tr(low))
        == a
    )
    return low, d


def main():
    rotations = [ident(2), rot(Q(4, 5), Q(3, 5)), rot(Q(7, 25), Q(24, 25))]
    edges = [(0, 1, ident(2)), (1, 2, ident(2)), (0, 2, rot(Q(-44, 125), Q(117, 125)))]
    lap = [[Q(0) for _ in range(6)] for _ in range(6)]
    objective = Q(0)
    for i, j, m in edges:
        assert mul(tr(m), m) == ident(2)
        prediction = mul(rotations[i], m)
        objective += sum(
            (rotations[j][a][b] - prediction[a][b]) ** 2 for a in range(2) for b in range(2)
        )
        for a in range(2):
            lap[2 * i + a][2 * i + a] += 1
            lap[2 * j + a][2 * j + a] += 1
            for b in range(2):
                lap[2 * i + a][2 * j + b] -= m[a][b]
                lap[2 * j + b][2 * i + a] -= m[a][b]
    rows = [sum((r[a] for r in rotations), []) for a in range(2)]
    assert all(
        mul(tr(r), r) == ident(2) and r[0][0] * r[1][1] - r[0][1] * r[1][0] == 1 for r in rotations
    )
    lam = Q(2, 5)
    slack = [[lap[i][j] - (lam if i == j else 0) for j in range(6)] for i in range(6)]
    low, d = ldl(slack)
    assert mul(slack, tr(rows)) == [[0, 0] for _ in range(6)]
    assert objective == 6 * lam == Q(12, 5)
    assert sum(v > 0 for v in d) == 4
    positions = [[Q(0), Q(0)], [Q(1), Q(0)], [Q(1), Q(1)]]
    translation_measurements = [[Q(1), Q(0)], [Q(3, 5), Q(4, 5)], [Q(1), Q(1)]]
    for (i, j, _), measurement in zip(edges, translation_measurements, strict=True):
        predicted = mul(rotations[i], [[x] for x in measurement])
        assert all(positions[j][k] - positions[i][k] == predicted[k][0] for k in range(2))
    # Four leading pivots positive: kernel determined by last two coordinates.
    # The last node block is invertible; alternatively any node block of R^T is.
    result = {
        "group": "SO(2)",
        "anchor": "R0=I",
        "objective": str(objective),
        "rotations": encode(rotations),
        "edges": [{"i": i, "j": j, "weight": "1", "measurement": encode(m)} for i, j, m in edges],
        "laplacian": encode(lap),
        "dual_node_scalars": [str(lam)] * 3,
        "slack": encode(slack),
        "ldl_L": encode(low),
        "ldl_D": encode(d),
        "rank": 4,
        "SE2_extension": {
            "positions": encode(positions),
            "translation_measurements_in_edge_order": encode(translation_measurements),
            "translation_weights": ["1", "1", "1"],
            "translation_objective": "0",
            "anchor": "R0=I,t0=(0,0)",
            "bridge": "Every translation residual contributes a nonnegative square, so the rotation certificate lower bound12/5 applies to the full SE2 objective. This feasible candidate has all translation residuals zero. Anchored rotation uniqueness plus connected zero translation residuals imply unique anchored positions. Not a general Schur-complement implementation.",
        },
        "proof_scope": "Exact rational feasibility, objective/dual equality, PSD factorization and complementary slackness. General trace weak duality and anchored kernel uniqueness are separately reviewed mathematical bridges, not a Lean proof yet.",
    }
    (HERE / "pm_rational_cycle.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"objective": str(objective), "rank": 4, "pivots": encode(d)}))


if __name__ == "__main__":
    main()
