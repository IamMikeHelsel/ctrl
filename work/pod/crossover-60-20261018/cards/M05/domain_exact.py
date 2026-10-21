"""Exact compatibility checks for M05; standard-library rationals only.

Run: uv run python work/pod/crossover-60-20261018/cards/M05/domain_exact.py
This checks finite rational pairs, not the six-dimensional norm conjecture.
"""

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

N = 6


def zeros(n=N, m=N):
    return [[F(0) for _ in range(m)] for _ in range(n)]


def transpose(a):
    return [list(col) for col in zip(*a, strict=True)]


def add(a, b):
    return [[x + y for x, y in zip(ar, br, strict=True)] for ar, br in zip(a, b, strict=True)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def sub(a, b):
    return add(a, scale(-1, b))


def mul(a, b):
    return [
        [sum(x * y for x, y in zip(row, col, strict=True)) for col in zip(*b, strict=True)]
        for row in a
    ]


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def inner(a, b):
    return sum(x * y for ar, br in zip(a, b, strict=True) for x, y in zip(ar, br, strict=True))


def identity():
    a = zeros()
    for i in range(N):
        a[i][i] = F(1)
    return a


def blocks(weights):
    a = zeros()
    for k, weight in enumerate(weights):
        a[2 * k][2 * k + 1] = F(weight)
        a[2 * k + 1][2 * k] = -F(weight)
    return a


def symmetric_basis():
    out = []
    for i in range(N):
        for j in range(i, N):
            a = zeros()
            a[i][j] = a[j][i] = F(1)
            out.append(a)
    return out


def skew_basis():
    out = []
    for i in range(N):
        for j in range(i + 1, N):
            a = zeros()
            a[i][j] = F(1)
            a[j][i] = F(-1)
            out.append(a)
    return out


def upper(a):
    return [a[i][j] for i in range(N) for j in range(i + 1, N)]


def unupper(vec):
    out = zeros()
    k = 0
    for i in range(N):
        for j in range(i + 1, N):
            out[i][j], out[j][i] = vec[k], -vec[k]
            k += 1
    return out


def rref(mat):
    a = [[F(x) for x in row] for row in mat]
    pivots = []
    row = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        d = a[row][col]
        a[row] = [x / d for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                d = a[i][col]
                a[i] = [x - d * y for x, y in zip(a[i], a[row], strict=True)]
        pivots.append(col)
        row += 1
        if row == len(a):
            break
    return a, pivots


def nullspace(mat):
    red, piv = rref(mat)
    out = []
    for col in range(len(mat[0])):
        if col in piv:
            continue
        vec = [F(0)] * len(mat[0])
        vec[col] = F(1)
        for row, pivot in enumerate(piv):
            vec[pivot] = -red[row][col]
        out.append(vec)
    return out


def inverse(a):
    red, piv = rref([row + ident for row, ident in zip(a, identity(), strict=True)])
    assert piv[:N] == list(range(N))
    return [row[N:] for row in red]


def phi(k, y, h):
    return sub(mul(mul(k, y), h), mul(h, mul(y, k)))


def phi_adjoint(k, y, w):
    return sub(mul(mul(y, k), w), mul(w, mul(k, y)))


def rhs(k, y):
    return sub(mul(mul(k, k), k), scale(F(1, 2), add(mul(mul(y, y), k), mul(k, mul(y, y)))))


def audit(name, k, y):
    sym, skew = symmetric_basis(), skew_basis()
    assert transpose(k) == scale(-1, k) and transpose(y) == scale(-1, y)
    cols = [upper(phi(k, y, h)) for h in sym]
    operator = transpose(cols)
    b = rhs(k, y)
    assert transpose(b) == scale(-1, b)
    rhs_vec = upper(b)
    rank = len(rref(operator)[1])
    aug_rank = len(rref([row + [v] for row, v in zip(operator, rhs_vec, strict=True)])[1])
    cokernel = [unupper(v) for v in nullspace(transpose(operator))]
    for w in cokernel:
        assert phi_adjoint(k, y, w) == zeros()
    for h in sym:
        for w in skew:
            assert inner(phi(k, y, h), w) == inner(h, phi_adjoint(k, y, w))
    pairings = [inner(w, b) for w in cokernel]
    assert (rank == aug_rank) == all(p == 0 for p in pairings)
    t = mul(y, k)
    delta = sub(mul(y, y), mul(k, k))
    power = identity()
    moments = []
    for _ in range(6):
        moments.append(trace(mul(power, delta)))
        power = mul(power, t)
    kinv = inverse(k)
    power = identity()
    polynomial_witnesses = []
    for moment in moments:
        w = mul(power, kinv)
        assert transpose(w) == scale(-1, w)
        assert phi_adjoint(k, y, w) == zeros()
        assert inner(w, b) == moment
        polynomial_witnesses.append(upper(w))
        power = mul(power, t)
    return {
        "name": name,
        "K": k,
        "Y": y,
        "K_rank": len(rref(k)[1]),
        "Y_rank": len(rref(y)[1]),
        "K_frobenius_squared": inner(k, k),
        "Y_frobenius_squared": inner(y, y),
        "YK": t,
        "moments_0_through_5": moments,
        "phi_rank": rank,
        "augmented_rank": aug_rank,
        "symmetric_nullity": 21 - rank,
        "cokernel_dimension": len(cokernel),
        "polynomial_witness_dimension_first_three": len(rref(polynomial_witnesses[:3])[1]),
        "pairing_equals_moment_checks": True,
        "cokernel_pairings": pairings,
        "RHS": b,
        "RHS_frobenius_squared": inner(b, b),
        "consistent": rank == aug_rank,
        "all_315_basis_adjoint_checks": True,
        "nonzero_obstruction": next(
            ({"W": w, "pairing": p} for w, p in zip(cokernel, pairings, strict=True) if p), None
        ),
    }


def main(output=None):
    cases = [
        ("distinct_roots_compatible", blocks([1, 2, 3]), blocks([1, 2, 3])),
        ("distinct_roots_incompatible", blocks([1, 2, 3]), blocks([2, 3, 4])),
        ("two_roots_compatible", blocks([1, 1, 2]), blocks([1, 1, 2])),
        ("two_roots_swap_obstruction", blocks([1, 2, 3]), blocks([2, 1, 3])),
        ("scalar_product_obstruction", blocks([1, 2, F(1, 2)]), blocks([1, F(1, 2), 2])),
        ("scalar_product_compatible", blocks([1, 1, 1]), blocks([1, 1, 1])),
    ]
    # A non-block-diagonal compatible candidate, generated by a rational involution.
    v = [[F(i)] for i in range(1, 7)]
    q = sub(identity(), scale(F(2, 91), mul(v, transpose(v))))
    assert mul(q, q) == identity()
    k = blocks([1, 2, 3])
    cases.append(("rational_householder_pair", k, mul(mul(q, k), q)))
    out = [audit(*case) for case in cases]
    assert [(r["phi_rank"], r["augmented_rank"]) for r in out[:6]] == [
        (12, 12),
        (12, 13),
        (8, 8),
        (8, 9),
        (0, 1),
        (0, 0),
    ]
    for row in [out[3], out[4]]:
        assert all(x == 0 for x in row["moments_0_through_5"])
        assert not row["consistent"]
    path = Path(output) if output else Path(__file__).with_name("domain_exact_results.json")
    path.write_text(json.dumps(out, indent=2, default=str) + "\n")
    for row in out:
        print(
            row["name"],
            "rank",
            row["phi_rank"],
            "aug",
            row["augmented_rank"],
            "moments",
            ",".join(map(str, row["moments_0_through_5"][:3])),
            "compatible",
            row["consistent"],
        )
    print("Saved", path)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    main(parser.parse_args().output)
