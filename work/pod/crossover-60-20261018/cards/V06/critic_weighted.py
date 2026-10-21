"""Independent consumer of the inventor's weighted rotational cycle."""

import json
from fractions import Fraction as F
from pathlib import Path

from critic_certificate import T, eye, product, proper, rank, rational


def cost(edges, R):
    return sum(
        w * sum((R[j][a][b] - product(R[i], m)[a][b]) ** 2 for a in range(2) for b in range(2))
        for i, j, w, m in edges
    )


def main():
    p = Path(__file__).resolve().parent
    cert = json.loads((p / "inventor_cycle.json").read_text())
    minus = [[-F(1), F(0)], [F(0), -F(1)]]
    edges = [(0, 1, F(15), minus), (1, 2, F(12), minus), (0, 2, F(20), minus)]
    assert [(i, j, F(w), rational(m)) for i, j, w, m in cert["edges"]] == edges
    R = [rational(a) for a in cert["candidate"]]
    mirror = [rational(a) for a in cert["other_gauge_fixed_optimum"]]
    assert R[0] == eye(2) and all(proper(a) for a in R + mirror) and R != mirror
    Q = [[F(0) for _ in range(6)] for _ in range(6)]
    for i, j, w, m in edges:
        for a in range(2):
            Q[2 * i + a][2 * i + a] += w
            Q[2 * j + a][2 * j + a] += w
            for b in range(2):
                Q[2 * i + a][2 * j + b] -= w * m[a][b]
                Q[2 * j + b][2 * i + a] -= w * m[a][b]
    lam = list(map(F, cert["dual_lambdas"]))
    B = rational(cert["slack_factor"])
    S = [[Q[i][j] - (lam[i // 2] if i == j else 0) for j in range(6)] for i in range(6)]
    assert S == product(T(B), B) and rank(S) == 2
    assert cost(edges, R) == cost(edges, mirror) == 2 * sum(lam) == 88
    rows = [[v for rot in R for v in rot[a]] for a in range(2)]
    assert product(rows, S) == [[0] * 6 for _ in range(2)]
    t = F(-1, 100)
    P = [
        [(1 - t * t) / (1 + t * t), -2 * t / (1 + t * t)],
        [2 * t / (1 + t * t), (1 - t * t) / (1 + t * t)],
    ]
    better = [R[0], product(R[1], P), R[2]]
    changed = [(i, j, F(13) if (i, j) == (1, 2) else w, m) for i, j, w, m in edges]
    assert cost(changed, R) == 92 and cost(changed, R) - cost(changed, better) == F(728, 10001)
    # Independently verify transformed directed edge conventions against original objective.
    frame = cert["frame_change"]
    fedges = [(i, j, F(w), rational(m)) for i, j, w, m in frame["edges"]]
    fposes = [rational(a) for a in frame["poses"]]
    reverse = [(j, i, w, T(m)) for i, j, w, m in fedges]
    wrong = [(j, i, w, m) for i, j, w, m in fedges]
    assert cost(fedges, fposes) == cost(reverse, fposes) == 88 and cost(wrong, fposes) != 88
    (p / "critic_weighted.json").write_text(
        json.dumps(
            {
                "objective": "88",
                "dual_gap": "0",
                "slack_rank": 2,
                "two_anchored_optima_verified": True,
                "weight_change_oldcost": "92",
                "strict_rational_improvement": "728/10001",
                "frame_correct_reversal_preserves_cost": True,
                "frame_wrong_reversal_cost": str(cost(wrong, fposes)),
                "producer_imports": False,
            },
            indent=2,
        )
        + "\n"
    )
    print("weighted certificate and edge semantics passed")


if __name__ == "__main__":
    main()
