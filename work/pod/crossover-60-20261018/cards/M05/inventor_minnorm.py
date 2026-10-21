"""Exact minimum-norm Phi solutions with primal/dual certificates."""

import json
from fractions import Fraction as F
from pathlib import Path

from inventor_exact import N, add, diagj, mul, rank, zeros
from inventor_perturb import eye, solve, transpose


def minimum(t):
    k = diagj([1, 2, 3])
    q0 = zeros()
    for i, j in enumerate([2, 3, 0, 1, 4, 5]):
        q0[i][j] = 1
    u = eye()
    c, s = (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)
    u[0][0] = u[4][4] = c
    u[0][4], u[4][0] = s, -s
    q = mul(mul(u, q0), transpose(u))
    y = mul(mul(q, k), q)
    k2, y2 = mul(k, k), mul(y, y)
    rhs = add(mul(k2, k), add(mul(y2, k), mul(k, y2)), F(-1, 2))
    bases, cols, gram = [], [], []
    for i in range(N):
        for j in range(i, N):
            h = zeros()
            h[i][j] = h[j][i] = F(1)
            bases.append(h)
            gram.append(F(1 if i == j else 2))
            phi = add(mul(mul(k, y), h), mul(h, mul(y, k)), -1)
            cols.append([phi[a][b] for a in range(N) for b in range(a + 1, N)])
    matrix = [list(r) for r in zip(*cols, strict=True)]
    b = [rhs[a][c] for a in range(N) for c in range(a + 1, N)]
    chosen = []
    indices = []
    for i, row in enumerate(matrix):
        if rank(chosen + [row]) > len(chosen):
            chosen.append(row)
            indices.append(i)
    bj = [b[i] for i in indices]
    dual_matrix = [
        [sum(x * y / g for x, y, g in zip(r, s, gram, strict=True)) for s in chosen] for r in chosen
    ]
    z = solve(dual_matrix, bj)
    hc = [sum(row[c] * v for row, v in zip(chosen, z, strict=True)) / gram[c] for c in range(21)]
    assert all(
        sum(x * y for x, y in zip(row, hc, strict=True)) == target
        for row, target in zip(matrix, b, strict=True)
    )
    norm2 = sum(g * h * h for g, h in zip(gram, hc, strict=True))
    dual = sum(x * y for x, y in zip(bj, z, strict=True))
    assert norm2 == dual
    # Verifying h=G^-1 M_J^T z is the stationarity certificate. Any feasible h+d
    # has cross term h^T G d=z^T M_J d=0, hence norm2 + d^T G d >= norm2.
    h = zeros()
    for coeff, basis in zip(hc, bases, strict=True):
        h = add(h, basis, coeff)
    kinv = diagj([-F(1), -F(1, 2), -F(1, 3)])
    a = mul(add(h, y, F(1, 2)), kinv)
    assert add(add(mul(a, k), mul(k, transpose(a))), y, -1) == zeros()
    assert add(add(mul(transpose(a), y), mul(y, a)), k, -1) == zeros()
    bound = F(1, 2) + norm2 / 14
    result = {
        "t": str(t),
        "Phi_rank": len(chosen),
        "independent_row_indices": indices,
        "Sym_basis_order": "lexicographic i<=j, Eii or Eij+Eji",
        "Skew_output_order": "lexicographic i<j upper coordinate",
        "gram_diagonal": list(map(str, gram)),
        "M": [list(map(str, row)) for row in matrix],
        "b": list(map(str, b)),
        "dual_z": list(map(str, z)),
        "minimum_H_coefficients": list(map(str, hc)),
        "all_15_constraints_exact": True,
        "both_original_pair_equations_exact": True,
        "minimum_H_frobenius_squared": str(norm2),
        "dual_b_dot_z": str(dual),
        "minimum_H_norm_approx": float(norm2) ** 0.5,
        "s_squared_lower_bound": str(bound),
        "s_squared_bound_approx": float(bound),
        "excludes_s_below_one_for_every_inner_choice": bound >= 1,
    }
    return result


results = [minimum(F(1, n)) for n in [2, 4, 8, 16, 32, 64]]
Path(__file__).with_name("inventor_minnorm.json").write_text(json.dumps(results, indent=2) + "\n")
print(
    json.dumps(
        [
            {
                k: r[k]
                for k in [
                    "t",
                    "minimum_H_frobenius_squared",
                    "minimum_H_norm_approx",
                    "s_squared_lower_bound",
                    "s_squared_bound_approx",
                ]
            }
            for r in results
        ],
        indent=2,
    )
)
