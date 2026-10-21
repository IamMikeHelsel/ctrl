"""Exact minimum-Frobenius probe of the involution-reduced affine family."""

import json
from fractions import Fraction as F
from pathlib import Path

from domain_exact import (
    add,
    blocks,
    identity,
    inner,
    mul,
    rref,
    scale,
    sub,
    symmetric_basis,
    transpose,
    upper,
    zeros,
)


def probe(weights, v_values, negatives):
    k = blocks(weights)
    v = [[F(x)] for x in v_values]
    reflection = sub(identity(), scale(2 / inner(v, v), mul(v, transpose(v))))
    signature = identity()
    for i in range(negatives):
        signature[i][i] = -1
    q = mul(mul(reflection, signature), reflection)
    assert mul(q, q) == identity()
    y = mul(mul(q, k), q)
    basis = symmetric_basis()
    operators = []
    for c in basis:
        a = mul(q, c)
        operators.append(upper(add(mul(a, k), mul(k, transpose(a)))))
    d = transpose(operators)
    b = upper(y)
    inv_weights = [1 / inner(c, c) for c in basis]
    gram = [
        [sum(d[i][p] * inv_weights[p] * d[j][p] for p in range(21)) for j in range(15)]
        for i in range(15)
    ]
    red, pivots = rref([row + [bi] for row, bi in zip(gram, b, strict=True)])
    if 15 in pivots:
        return {
            "weights": list(map(str, weights)),
            "v": v_values,
            "negative_signature": negatives,
            "consistent": False,
        }
    lam = [F(0)] * 15
    for row, pivot in enumerate(pivots):
        lam[pivot] = red[row][-1]
    coeff = [inv_weights[j] * sum(d[i][j] * lam[i] for i in range(15)) for j in range(21)]
    c = zeros()
    for coefficient, element in zip(coeff, basis, strict=True):
        c = add(c, scale(coefficient, element))
    a = mul(q, c)
    assert add(mul(a, k), mul(k, transpose(a))) == y
    assert add(mul(transpose(a), y), mul(y, a)) == k
    # Stationarity certificate C=D*lambda in the weighted symmetric coordinates.
    assert inner(c, c) == sum(x * y for x, y in zip(lam, b, strict=True))
    norm_squared = inner(c, c)
    return {
        "weights": list(map(str, weights)),
        "v": v_values,
        "negative_signature": negatives,
        "consistent": True,
        "B_frobenius_squared_min": str(norm_squared),
        "tester_Q_squared_lower_bound": str(4 * norm_squared / 6),
        "tester_Q_certifies_s_ge_1": norm_squared >= F(3, 2),
    }


def main():
    rows = []
    for weights in [[1, 2, 3], [1, 2, F(1, 2)]]:
        for v in [[1, 2, 3, 4, 5, 6], [2, 0, 1, -1, 3, 1]]:
            for negatives in [2, 3]:
                row = probe(weights, v, negatives)
                rows.append(row)
                print(row)
    path = Path(__file__).with_name("domain_involution_probe_results.json")
    path.write_text(json.dumps(rows, indent=2) + "\n")


if __name__ == "__main__":
    main()
