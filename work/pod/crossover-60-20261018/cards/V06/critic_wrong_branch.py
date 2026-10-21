"""Independent wrong stationary branch witness; exact algebra plus calculus bridge."""

import json
from fractions import Fraction as F
from pathlib import Path

from critic_certificate import eye, product, proper, rational
from critic_weighted import cost

P = Path(__file__).resolve().parent


def main():
    data = json.loads((P / "pm_wrong_branch.json").read_text())
    c, s = F(5, 13), F(12, 13)
    R = [[c, -s], [s, c]]
    R2 = product(R, R)
    M = product(R2, R)
    assert M == rational(data["measurement"])
    edges = [(0, 1, F(1), eye(2)), (1, 2, F(1), eye(2)), (0, 2, F(1), M)]
    old = [eye(2), R, R2]
    better = [eye(2)] + [rational(a) for a in data["better_rational_candidate"]]
    assert all(proper(a) for a in old + better)
    a, b = cost(edges, old), cost(edges, better)
    assert a == F(96, 13) and b == F(258992, 54925) and a - b == F(146608, 54925)
    # Angle residuals theta,theta,-theta. Analytic derivative 4 sin(angle).
    gradient = [4 * (s - s), 4 * (s - s)]
    assert gradient == [0, 0]
    H = [[8 * c, -4 * c], [-4 * c, 8 * c]]
    assert H[0][0] > 0 and H[0][0] * H[1][1] - H[0][1] ** 2 > 0
    # Leading scalar 2x2 slack corner after eliminating coordinate interleave.
    pivot = 2 * c - 1 / (2 * c)
    assert pivot == F(-69, 130)
    # Explicit vector gives negative quadratic value, avoiding LDL trust.
    z = [1 / (2 * c), F(1)]
    quadratic = 2 * c * (z[0] ** 2 + z[1] ** 2) - 2 * z[0] * z[1]
    assert quadratic == pivot < 0
    (P / "critic_wrong_branch.json").write_text(
        json.dumps(
            {
                "old_objective": str(a),
                "better_objective": str(b),
                "improvement": str(a - b),
                "stationary_angle_gradient": [str(v) for v in gradient],
                "Hessian": [[str(x) for x in row] for row in H],
                "negative_quadratic": str(quadratic),
                "negative_slack_vector_two_nodes": [str(v) for v in z],
                "scope": "Exact rational comparisons and algebra. Angle differentiation and strict-local-minimum inference are a hand calculus bridge, not a kernel theorem.",
            },
            indent=2,
        )
        + "\n"
    )
    print("wrong stationary branch independently verified")


if __name__ == "__main__":
    main()
