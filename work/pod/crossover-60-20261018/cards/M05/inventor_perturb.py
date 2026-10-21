"""Rational involution path, compatibility rank, and exact inverse-norm blowup bound."""

import json
from fractions import Fraction as F
from pathlib import Path

from inventor_exact import N, add, diagj, mul, rank, trace, zeros


def transpose(a):
    return [list(r) for r in zip(*a, strict=True)]


def eye():
    a = zeros()
    for i in range(N):
        a[i][i] = F(1)
    return a


def solve(a, b):
    m = [r + [v] for r, v in zip(a, b, strict=True)]
    pivots = []
    r = 0
    for j in range(len(a[0])):
        p = next((i for i in range(r, len(m)) if m[i][j]), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        v = m[r][j]
        m[r] = [x / v for x in m[r]]
        for i in range(len(m)):
            if i != r:
                v = m[i][j]
                m[i] = [x - v * y for x, y in zip(m[i], m[r], strict=True)]
        pivots.append(j)
        r += 1
    assert all(any(row[:-1]) or not row[-1] for row in m)
    x = [F(0) for _ in a[0]]
    for i, j in enumerate(pivots):
        x[j] = m[i][-1]
    return x


def experiment(t):
    k = diagj([1, 2, 3])
    q0 = zeros()
    for i, j in enumerate([2, 3, 0, 1, 4, 5]):
        q0[i][j] = 1
    u = eye()
    c, s = (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)
    u[0][0] = u[4][4] = c
    u[0][4], u[4][0] = s, -s
    q = mul(mul(u, q0), transpose(u))
    assert mul(q, q) == eye()
    y = mul(mul(q, k), q)
    k2, y2 = mul(k, k), mul(y, y)
    tt = mul(y, k)
    rhs = add(mul(k2, k), add(mul(y2, k), mul(k, y2)), F(-1, 2))
    delta = add(y2, k2, -1)
    moments = [trace(delta), trace(mul(tt, delta)), trace(mul(mul(tt, tt), delta))]
    assert not any(moments)
    basis = []
    cols = []
    for i in range(N):
        for j in range(i, N):
            h = zeros()
            h[i][j] = h[j][i] = F(1)
            basis.append(h)
            phi = add(mul(mul(k, y), h), mul(h, tt), -1)
            cols.append([phi[a][b] for a in range(N) for b in range(a + 1, N)])
    matrix = [list(r) for r in zip(*cols, strict=True)]
    right = [rhs[a][b] for a in range(N) for b in range(a + 1, N)]
    rk = rank(matrix)
    aug = rank([r + [v] for r, v in zip(matrix, right, strict=True)])
    w = diagj([1, 0, 0])
    # Reconstruct adjoint on Sym using orthogonal unnormalized basis.
    adj = zeros()
    for h, col in zip(basis, cols, strict=True):
        inner = 2 * col[0]  # <W,Phi(H)> uses first skew coordinate twice.
        size = sum(x * x for row in h for x in row)
        adj = add(adj, h, inner / size)
    b = -trace(mul(w, rhs))
    anorm2 = sum(x * x for row in adj for x in row)
    lower = b * b / anorm2 if anorm2 else None
    result = {
        "t": str(t),
        "rank": rk,
        "augmented_rank": aug,
        "moments": list(map(str, moments)),
        "pairing": str(b),
        "adjoint_norm_squared": str(anorm2),
        "H_frobenius_squared_lower_bound": str(lower),
        "H_norm_lower_bound_approx": float(lower) ** 0.5 if lower else None,
    }
    if rk == aug:
        hs = solve(matrix, right)
        h = zeros()
        for v, bas in zip(hs, basis, strict=True):
            h = add(h, bas, v)
        kinv = diagj([-F(1), -F(1, 2), -F(1, 3)])
        a = mul(add(h, y, F(1, 2)), kinv)
        first = add(add(mul(a, k), mul(k, transpose(a))), y, -1)
        second = add(add(mul(transpose(a), y), mul(y, a)), k, -1)
        assert first == zeros() and second == zeros()
        result["both_original_pair_equations_exact"] = True
        result["A_particular_frobenius_squared"] = str(sum(x * x for row in a for x in row))
    return result


results = [experiment(F(0))] + [experiment(F(1, n)) for n in [2, 4, 8, 16, 32, 64]]
Path(__file__).with_name("inventor_perturb.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps(results, indent=2))
