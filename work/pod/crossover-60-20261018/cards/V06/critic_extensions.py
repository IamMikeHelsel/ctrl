"""Independent SE2 extension and weighted phase boundary checks."""

import copy
import json
from fractions import Fraction as F
from pathlib import Path

from critic_certificate import T, product, rank, rational
from critic_weighted import cost

P = Path(__file__).resolve().parent


def translation_cost(positions, rotations, edges, measurements, weights):
    return sum(
        w
        * sum(
            (positions[j][k] - positions[i][k] - sum(rotations[i][k][l] * m[l] for l in range(2)))
            ** 2
            for k in range(2)
        )
        for (i, j), m, w in zip(edges, measurements, weights, strict=True)
    )


def main():
    data = json.loads((P / "pm_rational_cycle.json").read_text())
    se = data["SE2_extension"]
    R = [rational(r) for r in data["rotations"]]
    pos = rational(se["positions"])
    m = rational(se["translation_measurements_in_edge_order"])
    w = list(map(F, se["translation_weights"]))
    assert pos == [[0, 0], [1, 0], [1, 1]]
    assert m == [[1, 0], [F(3, 5), F(4, 5)], [1, 1]] and w == [1, 1, 1]
    edges = [(0, 1), (1, 2), (0, 2)]
    assert translation_cost(pos, R, edges, m, w) == 0
    changed = copy.deepcopy(m)
    changed[1][0] += F(1, 100)
    changed_cost = translation_cost(pos, R, edges, changed, w)
    assert changed_cost == F(1, 10000)
    # Lower rotation bound survives; the old primal no longer ATTAINS it.
    # Correct reversal in SE2 is (M^T,-M^T t), not just -t.
    M = [rational(e["measurement"]) for e in data["edges"]]
    rm = [
        [-sum(T(mm)[k][l] * v[l] for l in range(2)) for k in range(2)]
        for mm, v in zip(M, m, strict=True)
    ]
    # When rotational residual is nonzero, reversing this directed statistical
    # objective changes the translation term unless the noise model is transformed.
    reversed_cost = translation_cost(pos, R, [(j, i) for i, j in edges], rm, w)
    assert reversed_cost > 0
    phase = json.loads((P / "inventor_phase.json").read_text())
    S = rational(phase["slack"])
    a, b = [F(7), F(3), F(4)], [F(0), F(1), F(-1)]
    assert S == [
        [F(8, 7) * a[i] * a[j] + F(12, 7) * b[i] * b[j] for j in range(3)] for i in range(3)
    ]
    assert rank(S) == 2 and product(S, [[1], [-1], [-1]]) == [[0], [0], [0]]
    minus = [[-F(1), F(0)], [F(0), -F(1)]]
    ident = [[F(1), F(0)], [F(0), F(1)]]
    pedges = [(0, 1, F(24), minus), (1, 2, F(12), minus), (0, 2, F(32), minus)]
    assert cost(pedges, [ident, minus, minus]) == 96
    (P / "critic_extensions.json").write_text(
        json.dumps(
            {
                "SE2_translation_cost": "0",
                "translation_mutation_old_candidate_excess": str(changed_cost),
                "reversed_SE2_translation_cost": str(reversed_cost),
                "reversed_SE2_scope": "Direction of translational statistical residual is model data; an inverse group measurement does not preserve this residual when rotational errors are nonzero.",
                "phase_cost": "96",
                "phase_rank": 2,
                "phase_unique_kernel": [1, -1, -1],
                "scope": "Exact independent rational arithmetic plus separately stated nonnegative-square/anchored-kernel arguments.",
            },
            indent=2,
        )
        + "\n"
    )
    print("SE2 and phase checks passed; inverse-direction translation objective changes")


if __name__ == "__main__":
    main()
