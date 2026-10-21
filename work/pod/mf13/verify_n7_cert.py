"""Independent exact check of proof/cert_n7.json: k(A)^2 >= ||L_A K||^2/||K||^2 > c >= s(A)^2.

The skew lower bound is exact (rational). The symmetric upper bound checks that c*G - M is
positive semidefinite by exact LDL over Fractions, where M is the Gram matrix of L_A on the
(non-normalised) symmetric basis and G the Frobenius Gram matrix of that basis.
"""

import json
from fractions import Fraction as F
from pathlib import Path

d = json.loads((Path(__file__).parent / "proof" / "cert_n7.json").read_text())
A = [[F(x) for x in row] for row in d["A"]]
K = [[F(x) for x in row] for row in d["K"]]
n = len(A)


def mul(X, Y):
    return [[sum(X[i][k] * Y[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def T(X):
    return [list(r) for r in zip(*X)]


def lyap(X):
    P, Q = mul(A, X), mul(X, T(A))
    return [[P[i][j] + Q[i][j] for j in range(n)] for i in range(n)]


def fro2(X):
    return sum(x * x for r in X for x in r)


assert all(K[i][j] == -K[j][i] for i in range(n) for j in range(n))
k_lower = fro2(lyap(K)) / fro2(K)

basis = []
for i in range(n):
    for j in range(i, n):
        E = [[F(0)] * n for _ in range(n)]
        E[i][j] = E[j][i] = F(1)
        basis.append(E)
imgs = [lyap(E) for E in basis]


def ip(X, Y):
    return sum(X[i][j] * Y[i][j] for i in range(n) for j in range(n))


m = len(basis)
M = [[ip(imgs[a], imgs[b]) for b in range(m)] for a in range(m)]
G = [[ip(basis[a], basis[b]) for b in range(m)] for a in range(m)]


def psd_exact(Q):
    Q = [row[:] for row in Q]
    for p in range(len(Q)):
        if Q[p][p] < 0:
            return False
        if Q[p][p] == 0:
            if any(Q[p][j] != 0 for j in range(p, len(Q))):
                return False
            continue
        for i in range(p + 1, len(Q)):
            f = Q[i][p] / Q[p][p]
            for j in range(p, len(Q)):
                Q[i][j] -= f * Q[p][j]
    return True


# Pick c strictly between: use the certificate's c if present, else bisect on rationals.
c = F(d["c"][0], d["c"][1]) if isinstance(d["c"], list) else F(d["c"])
q = F(d["q"][0], d["q"][1])
print("k^2 lower bound (exact) ~", float(k_lower))
print("certificate c ~", float(c), " q ~", float(q))
ok_sym = psd_exact([[c * G[a][b] - M[a][b] for b in range(m)] for a in range(m)])
print("c*G - M PSD (so s^2 <= c):", ok_sym)
print("k^2 > c:", k_lower > c)
if ok_sym and k_lower > c:
    print("VERIFIED: k(A)/s(A) >= sqrt(k_lower/c) ~", float(k_lower / c) ** 0.5)
