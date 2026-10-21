"""Independent rational reproduction of the near-stratum norm exclusion gate."""

import json
from fractions import Fraction as F
from pathlib import Path

from domain_exact import add, blocks, identity, inner, mul, phi_adjoint, rhs, scale, transpose


def main():
    k = blocks([1, 2, 3])
    w = blocks([1, 0, 0])
    swap = [[F(int(j == [2, 3, 0, 1, 4, 5][i])) for j in range(6)] for i in range(6)]
    records = []
    for t in [F(1, 2**j) for j in range(1, 7)]:
        cosine, sine = (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)
        rotation = identity()
        rotation[0][0] = rotation[4][4] = cosine
        rotation[0][4], rotation[4][0] = -sine, sine
        qmat = mul(mul(rotation, swap), transpose(rotation))
        assert mul(qmat, qmat) == identity()
        y = mul(mul(qmat, k), qmat)
        norm_squared = inner(k, k)
        assert norm_squared == inner(y, y) == 28
        r = rhs(k, y)
        adj = phi_adjoint(k, y, w)
        pairing, adj_squared = inner(w, r), inner(adj, adj)
        assert adj_squared > 0
        h_bound = pairing**2 / adj_squared
        s_bound = F(1, 2) + 2 * h_bound / norm_squared
        records.append(
            {
                "t": str(t),
                "K": k,
                "Y": y,
                "W": w,
                "q": str(norm_squared),
                "pairing_W_R": str(pairing),
                "adjoint_squared": str(adj_squared),
                "H_squared_lower_bound": str(h_bound),
                "s_squared_lower_bound": str(s_bound),
                "excludes_s_below_1": s_bound >= 1,
            }
        )
    assert [r["excludes_s_below_1"] for r in records] == [False, True, True, True, True, True]
    # Exact rank-one identity for a nonnormal rational matrix and a non-unit vector.
    a = [[F((i + 2) * (j + 1) - 4 * (i == j), 7) for j in range(6)] for i in range(6)]
    x = [[F(i - 2, 3)] for i in range(6)]
    ax = mul(a, x)
    s = mul(x, transpose(x))
    output = add(mul(a, s), mul(s, transpose(a)))
    assert inner(output, output) == 2 * inner(ax, ax) * inner(x, x) + 2 * inner(x, ax) ** 2
    # Symmetric/skew orthogonality is exact, with no positive-definiteness premise.
    h = add(a, transpose(a))
    assert inner(h, k) == 0
    assert inner(add(h, scale(F(1, 2), k)), add(h, scale(F(1, 2), k))) == (
        inner(h, h) + inner(k, k) / 4
    )
    path = Path(__file__).with_name("domain_norm_gate_results.json")
    path.write_text(json.dumps(records, indent=2, default=str) + "\n")
    for record in records:
        print(record["t"], record["s_squared_lower_bound"], record["excludes_s_below_1"])


if __name__ == "__main__":
    main()
