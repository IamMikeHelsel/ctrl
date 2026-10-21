"""E12: monotone alternating ascent for k/s:
   (K_t, Y_t) = top skew singular pair of L_{A_t};  A_{t+1} = SDP-dual maximiser of <A, Y_t K_t> s.t. s(A) <= 2.
   ratio(A_t) <= N(Y_t K_t) <= ratio(A_{t+1}).  Fixed points satisfy the KKT condition of max k/s.
   Usage: e12_mm_ascent.py n seed nstarts iters [init: gauss|file.npy]"""
import sys, json, warnings
warnings.filterwarnings('ignore')
import numpy as np
from core import *
from staticN import N_of

n, seed, nst, iters = map(int, sys.argv[1:5]); init = sys.argv[5] if len(sys.argv) > 5 else 'gauss'
rng = np.random.default_rng(seed)
def ratio(A): return np.linalg.norm(BK(A), 2) / np.linalg.norm(BS(A), 2)
best = (0, None)
for st in range(nst):
    if init == 'gauss': A = rng.standard_normal((n, n))
    elif init == 'sparse': A = rng.standard_normal((n, n)) * (rng.random((n, n)) < 0.4)
    else: A = np.load(init) + 0.02 * st * rng.standard_normal((n, n))
    r0 = ratio(A); hist = []
    for it in range(iters):
        u, s, vt = np.linalg.svd(BK(A)); K = skew_of(vt[0], n); Y = skew_of(u[:, 0], n)
        N, W, G = N_of(Y @ K, return_W=True)
        A = max([G, G.T], key=ratio); r = ratio(A); hist.append(r)
        if it > 3 and hist[-1] - hist[-4] < 1e-9: break
    sv = np.linalg.svd(K, compute_uv=False)[::2]
    print(json.dumps(dict(start=st, r0=r0, r=r, N=N, it=it, mK=np.round(sv, 4).tolist())), flush=True)
    np.save(f'logs/e12_n{n}_s{seed}_{init.split("/")[-1]}_end{st}.npy', A)
    if r > best[0]:
        best = (r, A); np.save(f'logs/e12_n{n}_s{seed}_{init.split("/")[-1]}_best.npy', A)
print("BEST", best[0])
