"""Baseline (as in Kressner-Vandereycken Sec. 4): Adam on g(A)=k(A)-s(A) on the Frobenius sphere. usage: adam_gap.py N NSTARTS SEED"""
import sys, time, json
import numpy as np
from bl import *

n = int(sys.argv[1]); nst = int(sys.argv[2]); seed = int(sys.argv[3])
TS, TK = optensors(n)
rng = np.random.default_rng(seed)


def gap_grad(A):
    BSm = BS(A); BKm = BK(A)
    us, ss, vts = np.linalg.svd(BSm); uk, sk, vtk = np.linalg.svd(BKm)
    gs = np.einsum('i,pqij,j->pq', us[:, 0], TS, vts[0])
    gk = np.einsum('i,pqij,j->pq', uk[:, 0], TK, vtk[0])
    return sk[0] - ss[0], gk - gs, ss[0], sk[0]


def run(A, lr0=0.02, iters=800, lr1=0.006, iters2=400):
    m = np.zeros_like(A); v = np.zeros_like(A); t = 0
    best = (-1e9, None)
    for stage, (lr, its) in enumerate(((lr0, iters), (lr1, iters2))):
        for it in range(its):
            t += 1
            g, grad, s, k = gap_grad(A)
            if g > best[0]: best = (g / np.linalg.norm(A) if False else g, A.copy())
            grad = grad - np.sum(grad * A) * A   # tangent on sphere
            m = 0.9 * m + 0.1 * grad; v = 0.999 * v + 0.001 * grad**2
            mh = m / (1 - 0.9**t); vh = v / (1 - 0.999**t)
            lrt = lr * (0.15 + 0.85 * (1 - it / its)**2)
            A = A + lrt * mh / (np.sqrt(vh) + 1e-8)
            A = A / np.linalg.norm(A)
    g, grad, s, k = gap_grad(A)
    if g > best[0]: best = (g, A.copy())
    return best


res = []
for st in range(nst):
    A = rng.standard_normal((n, n)); A /= np.linalg.norm(A)
    g, Ab = run(A)
    s, k = norms(Ab)
    res.append(g)
    print(f"n={n} start {st}: best gap k-s = {g:.3e}  (s={s:.6f}, k={k:.6f}, rel {(k-s)/s:.2e})", flush=True)
    if g > 1e-7:
        json.dump(Ab.tolist(), open(f'runs/adam_n{n}_s{seed}_{st}.json', 'w'))
print("positive gaps:", sum(1 for g in res if g > 1e-7), "/", len(res))
