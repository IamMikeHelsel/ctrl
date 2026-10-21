"""Independent derivative recursion, not the producer Taylor-series implementation."""

import json
import math
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
I = [[F(i == j) for j in range(3)] for i in range(3)]
X = [[F(0), F(0), F(0)], [F(0), F(0), F(-1)], [F(0), F(1), F(0)]]
Y = [[F(0), F(0), F(1)], [F(0), F(0), F(0)], [F(-1), F(0), F(0)]]
Z = [[F(0), F(-1), F(0)], [F(1), F(0), F(0)], [F(0), F(0), F(0)]]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def mv(a, v):
    return [sum(a[i][j] * v[j] for j in range(3)) for i in range(3)]


def combine(*terms):
    return [[sum(c * a[i][j] for c, a in terms) for j in range(3)] for i in range(3)]


def main():
    # Ordinary derivatives at0 from repeated product rule.
    r = [I, Z, combine((1, mul(Z, Z)), (1, X)), combine((1, mul(mul(Z, Z), Z)), (3, mul(Z, X)))]
    dmat = [
        I,
        combine((1, Y), (2, Z)),
        combine((1, mul(Y, Y)), (4, mul(Y, Z)), (4, mul(Z, Z))),
        combine(
            (1, mul(mul(Y, Y), Y)),
            (6, mul(mul(Y, Y), Z)),
            (12, mul(Y, mul(Z, Z))),
            (8, mul(mul(Z, Z), Z)),
        ),
    ]
    d = [mv(a, [1, 0, 0]) for a in dmat]
    p = []
    for n in range(4):
        previous = [F(0)] * 3
        for k in range(1, n + 1):
            term = mv(r[k], p[n - k])
            previous = [a + math.comb(n, k) * b for a, b in zip(previous, term, strict=True)]
        p.append([a - b for a, b in zip(d[n], previous, strict=True)])
    source = json.loads((HERE / "inventor_frame_jets.json").read_text())
    assert d == [[F(x) for x in row] for row in source["world_jets"]]
    assert p == [[F(x) for x in row] for row in source["relative_jets"]]
    assert p[3] == [0, -1, 10]
    # Constant worlde1 under R=exp(tZ): p'=-Ze1, p''=Z²e1.
    pos = [F(1), F(0), F(0)]
    vel = [F(0), F(-1), F(0)]
    missing = [a + 2 * b for a, b in zip(mv(mul(Z, Z), pos), mv(Z, vel), strict=True)]
    assert missing == [1, 0, 0]
    # PassiveframeQ=Rz90: Rnew=Q, pnew=Q^T e1, wrong unchanged p'=-e2.
    q = [[0, -1, 0], [1, 0, 0], [0, 0, 1]]
    incorrect = [a + b for a, b in zip(mv(Z, pos), mv(q, vel), strict=True)]
    assert incorrect == [1, 1, 0]
    data = {
        "world_derivatives": [[str(x) for x in row] for row in d],
        "relative_derivatives": [[str(x) for x in row] for row in p],
        "missing_centripetal_world_acceleration": list(map(str, missing)),
        "untransported_velocity_world_error": list(map(str, incorrect)),
        "scope": "Exact pointwise jet identities of smooth rotation paths; not gimbal joint derivatives or actuator dynamics.",
    }
    (HERE / "critic_jets.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
