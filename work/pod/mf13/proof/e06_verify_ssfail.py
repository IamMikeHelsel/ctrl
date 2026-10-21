"""E06: independent verification that the same-square (Chen-Tian) class fails at the top skew vector
for the CMA-found A (logs/e05_n6_s1_e0.05_best.npy):
  * top skew singular triple by full 36x36 Kronecker (independent of core.BK)
  * max over ALL same-square symmetric S (S^2 = -K^2): components diag(k_i X_i), X_i in {R(theta), +I, -I}
    via dense grid + polish; also mpmath check of the best value.
  * s(A), k(A), gap k2/k1."""
import sys, itertools
import numpy as np
from scipy.optimize import minimize
from core import *
from ssclass import frame

fn = sys.argv[1] if len(sys.argv) > 1 else 'logs/e05_n6_s1_e0.05_best.npy'
A = np.load(fn); n = A.shape[0]
# Kronecker operator, column-major vec
I = np.eye(n); M = np.kron(I, A) + np.kron(A, I)
P = np.zeros((n * n, n * n))
for i in range(n):
    for j in range(n):
        P[j * n + i, i * n + j] = 1
def rng_basis(Pr):
    u, s, vt = np.linalg.svd(Pr); return u[:, s > 0.5]
Us = rng_basis((np.eye(n * n) + P) / 2); Uk = rng_basis((np.eye(n * n) - P) / 2)
sS = np.linalg.svd(Us.T @ M @ Us, compute_uv=False)
u, sK, vt = np.linalg.svd(Uk.T @ M @ Uk)
print("s(A) =", sS[0], " k(A) =", sK[0], " k2/k1 =", sK[1] / sK[0], " s/k =", sS[0] / sK[0])
K = (Uk @ vt[0]).reshape(n, n, order='F'); K = (K - K.T) / 2; K /= np.linalg.norm(K)
print("check singular vector:", np.linalg.norm(L(A.T, L(A, K)) - sK[0] ** 2 * K))
F, w = frame(K); print("moduli", w)
def S_of(choice, th):
    D = np.zeros((n, n))
    for i in range(3):
        c = choice[i]
        if c == 'R': X = np.array([[np.cos(th[i]), np.sin(th[i])], [np.sin(th[i]), -np.cos(th[i])]])
        elif c == '+': X = np.eye(2)
        else: X = -np.eye(2)
        D[2*i:2*i+2, 2*i:2*i+2] = abs(w[i]) * X
    return F @ D @ F.T
best = (0, None)
for choice in itertools.product('R+-', repeat=3):
    nR = choice.count('R')
    def neg(th): return -np.linalg.norm(L(A, S_of(choice, th)))
    g = np.random.default_rng(0).uniform(0, 2 * np.pi, (400 if nR else 1, 3))
    vals = [neg(t) for t in g]
    for i in np.argsort(vals)[:5]:
        r = minimize(neg, g[i], method='Nelder-Mead', options=dict(xatol=1e-12, fatol=1e-14, maxiter=4000))
        if -r.fun > best[0]: best = (-r.fun, (choice, r.x))
    print(choice, "max ||L_A S||/k =", -min(vals) / sK[0] if nR == 0 else max(-r.fun, -min(vals)) / sK[0])
S = S_of(*best[1])
print("same-square check |S^2+K^2| =", np.linalg.norm(S @ S + K @ K), " |S| =", np.linalg.norm(S))
print("BEST same-square ratio ||L_A S||/(k ||S||) =", best[0] / sK[0])
import mpmath as mp
mp.mp.dps = 40
Am = mp.matrix(A.tolist()); Sm = mp.matrix(S.tolist())
LS = Am * Sm + Sm * Am.T
print("mpmath ||L_A S||_F =", mp.sqrt(sum(LS[i, j] ** 2 for i in range(n) for j in range(n))), " k =", sK[0])
