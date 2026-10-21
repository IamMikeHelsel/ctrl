"""Exact certificate for the MM-ascended n=7 counterexample.
A integer (rounded from logs/n7_dual_best.npy scaled), K integer skew.  With exact rational arithmetic:
  (1) q := ||L_A K||_F^2 / ||K||_F^2   (exact)       ->  k(A)^2 >= q
  (2) c rational with c*I - B^T B > 0 (exact LDL^T, all pivots > 0), B = matrix of L_A on Sym_7 in the
      basis {E_ii} U {(E_ij+E_ji)/sqrt2}; the sqrt2's are handled by working with the Gram form
      <X, L_A^* L_A X> / <X,X> over integer coordinates: we certify  c*<X,X> - ||L_A X||^2  is PD as a quadratic form
      on Sym_7 with coordinates x_ij (i<=j), using the integer Gram matrices.
  q > c  =>  k(A) > s(A)."""
import json, numpy as np
from fractions import Fraction as Fr
from core import BK, BS, skew_of

A0 = np.load('logs/n7_dual_best.npy'); n = 7
scale = 200 / np.abs(A0).max()
A = np.rint(A0 * scale).astype(int)
Af = A.astype(float)
print("float ratio of integer A:", np.linalg.norm(BK(Af), 2) / np.linalg.norm(BS(Af), 2))
u, s, vt = np.linalg.svd(BK(Af)); Kf = skew_of(vt[0], n)
K = np.rint(Kf / np.abs(Kf).max() * 1000).astype(int); K = np.triu(K, 1); K = K - K.T

Ai = [[int(v) for v in row] for row in A.tolist()]
def LA(X):  # exact (python ints)
    return [[sum(Ai[i][k] * X[k][j] for k in range(n)) + sum(X[i][k] * Ai[j][k] for k in range(n)) for j in range(n)] for i in range(n)]
Ki = [[int(K[i, j]) for j in range(n)] for i in range(n)]
LK = LA(Ki)
q = Fr(sum(v * v for row in LK for v in row), sum(v * v for row in Ki for v in row))
print("q = ||L_A K||^2/||K||^2 =", float(q))

# quadratic forms on Sym_7 in coordinates x_ij (i<=j): X_ij = X_ji = x_ij
idx = [(i, j) for i in range(n) for j in range(i, n)]
def Xof(e):
    X = [[0] * n for _ in range(n)]; i, j = idx[e]; X[i][j] = 1; X[j][i] = 1; return X
cols = [LA(Xof(e)) for e in range(len(idx))]
M = len(idx)
Gram = [[sum(cols[a][i][j] * cols[b][i][j] for i in range(n) for j in range(n)) for b in range(M)] for a in range(M)]
Nrm = [[0] * M for _ in range(M)]
for a, (i, j) in enumerate(idx): Nrm[a][a] = 1 if i == j else 2
smax2 = np.linalg.norm(BS(Af), 2) ** 2
c = Fr(smax2 * (1 + 1e-4)).limit_denominator(10 ** 6)
print("c =", float(c), " (s^2 float =", smax2, ")")
Q = [[c * Nrm[a][b] - Gram[a][b] for b in range(M)] for a in range(M)]
# exact LDL^T
piv = []
Qm = [row[:] for row in Q]
ok = True
for k in range(M):
    p = Qm[k][k]; piv.append(p)
    if p <= 0: ok = False; break
    for i in range(k + 1, M):
        if Qm[i][k] != 0:
            f = Qm[i][k] / p
            for j in range(k + 1, M): Qm[i][j] -= f * Qm[k][j]
print("LDL^T all pivots > 0:", ok, " min pivot =", float(min(piv)))
print("certified: k^2 >= q =", float(q), " > c >= s^2 :", ok and q > c, "  => k/s >", float(q / c) ** 0.5)
json.dump(dict(A=A.tolist(), K=K.tolist(), q=[int(q.numerator), int(q.denominator)], c=[int(c.numerator), int(c.denominator)],
               ldl_ok=ok, ratio_lower_bound=float(q / c) ** 0.5), open('cert_n7.json', 'w'))
