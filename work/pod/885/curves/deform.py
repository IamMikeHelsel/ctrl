"""First-order deformations of a polynomial grid pattern (rows a_i^2, a_i quadratic; columns C_j
quartic, one column fixed = 0) at the Lagrange point.

Entry (i,j): a_i^2 + C_j = b_ij^2.  Tangent: 2 a_i da_i + dC_j - 2 b_ij db_ij = 0 (5 coefficient
equations).  Trivial directions: GL2 on (u,v) (4-dim; scalars = value scaling).
Prints dim(tangent) - 4 for several incidence patterns.
"""
import json
from famext import pari

d = json.load(open("poly77_lagrange.json"))
R = [pari(r) for r in d["R"]]
C = [pari(c) for c in d["C"]]
ZERO = 3
from famext import pari as _p
msq = pari("msq")
A = [msq(r) for r in R]
inc = {(i, j) for i in range(7) for j in range(7) if pari.issquare(R[i] + C[j])}
B = {(i, j): (msq(R[i] + C[j]) if R[i] + C[j] != 0 else pari(0)) for (i, j) in inc}


def coeffs(p, n):
    return [pari.polcoef(p, k, "x") for k in range(n)]


def tangent_dim(rows, cols):
    pat = [(i, j) for (i, j) in inc if i in rows and j in cols]
    var = []
    for i in rows:
        var += [("a", i, k) for k in range(3)]
    for j in cols:
        if j != ZERO:
            var += [("C", j, k) for k in range(5)]
    for e in pat:
        var += [("b", e, k) for k in range(3)]
    idx = {v: n for n, v in enumerate(var)}
    eqs = []
    x = pari("x")
    for (i, j) in pat:
        rowsE = [[0] * len(var) for _ in range(5)]
        for k in range(3):
            p = coeffs(2 * A[i] * x ** k, 5)
            for m in range(5):
                rowsE[m][idx[("a", i, k)]] += p[m]
            p = coeffs(-2 * B[(i, j)] * x ** k, 5)
            for m in range(5):
                rowsE[m][idx[("b", (i, j), k)]] += p[m]
        if j != ZERO:
            for k in range(5):
                rowsE[k][idx[("C", j, k)]] += 1
        eqs += rowsE
    M = pari.matrix(len(eqs), len(var), [c for r in eqs for c in r])
    rk = int(pari.matrank(M))
    return len(pat), len(var), rk, len(var) - rk - 4


if __name__ == "__main__":
    pats = {
        "lagrange4x4": ([0, 1, 2, 3], [0, 1, 2, 3]),
        "3x7 (rows 0,2,3)": ([0, 2, 3], list(range(7))),
        "7x3 (cols 1,2,3)": (list(range(7)), [1, 2, 3]),
        "core3x3+row1+col0+rows456": (list(range(7)), [0, 1, 2, 3]),
        "full 7x7 pattern": (list(range(7)), list(range(7))),
        "core 3x3": ([0, 2, 3], [1, 2, 3]),
        "core+col0 (3x4)": ([0, 2, 3], [0, 1, 2, 3]),
    }
    for k, (r, c) in pats.items():
        print(f"{k:32s} entries,vars,rank,moduli-tangent = {tangent_dim(r, c)}")
