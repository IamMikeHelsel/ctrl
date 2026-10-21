"""Independent skew-matrix reconstruction of the local Cayley cell and stored points."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def rotation(v):
    a, b, c = v
    k = [[F(0), -c, b], [c, F(0), -a], [-b, a, F(0)]]
    kk = [[sum(k[i][t] * k[t][j] for t in range(3)) for j in range(3)] for i in range(3)]
    scale = 2 / (1 + sum(x * x for x in v))
    return [[F(i == j) + scale * (k[i][j] + kk[i][j]) for j in range(3)] for i in range(3)]


def main():
    maximum = F(0)
    for v in itertools.product([F(i, 800) for i in range(-2, 3)], repeat=3):
        r = rotation(v)
        for i, j in itertools.product(range(3), repeat=2):
            assert sum(r[t][i] * r[t][j] for t in range(3)) == F(i == j)
        determinant = sum(
            sign * r[0][perm[0]] * r[1][perm[1]] * r[2][perm[2]]
            for perm, sign in [
                ((0, 1, 2), 1),
                ((1, 2, 0), 1),
                ((2, 0, 1), 1),
                ((0, 2, 1), -1),
                ((2, 1, 0), -1),
                ((1, 0, 2), -1),
            ]
        )
        assert determinant == 1
        f2 = sum((r[i][j] - F(i == j)) ** 2 for i, j in itertools.product(range(3), repeat=2))
        s = sum(x * x for x in v)
        assert f2 == 8 * s / (1 + s) <= F(1, 2500)
        maximum = max(maximum, f2)
    assert maximum == F(24, 160003)
    producer = json.loads((HERE / "pm_cell.json").read_text())
    assert F(producer["max_frobenius_squared"]) == maximum
    # Recompute generic rectified payloads using literal two-camera projections.
    rect = json.loads((HERE / "domain_rectified_exact.json").read_text())
    for row in rect["cases"]:
        d, c, s = (F(row[k]) for k in ("disparity", "vertical", "s"))
        x, y, z = map(F, row["point"])
        assert z > 0 and F(3, 2) / z == s
        r1 = (x / z - d, y / z - F(1, 3))
        r2 = ((x - F(3, 2)) / z, y / z - F(1, 3) - c)
        expected = ((s - d) ** 2 + c * c) / 4
        assert (
            sum(t * t for t in r1) == sum(t * t for t in r2) == expected == F(row["squared_error"])
        )
    assert len(rect["cases"]) == 36
    h = (F(4), F(-2), F(5))
    bh = (h[0] + h[2], h[1] - h[2] / 2)
    assert sum(x * x for x in bh) == F(9, 4) * sum(x * x for x in h)
    delta = F(1, 20)
    k = delta * F(8, 5)
    enlarged = (F(1, 10) + F(3, 2) * k) / (1 - k)
    assert enlarged == F(11, 46) < F(1, 4)
    assert F(24, 10003) < delta * delta
    assert (F(1, 10) + F(3, 2) * F(3, 56) * F(8, 5)) / (1 - F(3, 56) * F(8, 5)) == F(1, 4)
    q = F(1, 400)
    vector_change_squared = 4 * q * q / (1 + q * q)
    frobenius_squared = 8 * q * q / (1 + q * q)
    assert vector_change_squared > frobenius_squared * frobenius_squared
    data = {
        "norm_squared_as_norm_mutation": "rejected by exact unit-vector change",
        "independent_cayley_grid": 125,
        "max_frobenius_squared": str(maximum),
        "rectified_payloads_recomputed": 36,
        "residual_map_norm_squared": "9/4",
        "larger_cell": {
            "coordinate_halfwidth": "1/100",
            "frobenius_squared_max": "24/10003",
            "delta": "1/20",
            "enlarged": "11/46",
            "sufficient_budget_cutoff": "3/56",
        },
        "scope": "Exact finite replays plus rational budget arithmetic; not a full SO3 cover or optimal cell-size theorem.",
    }
    (HERE / "critic_cell.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
