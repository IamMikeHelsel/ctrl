import json, numpy as np
from core import *
from ssclass import comp_mats, oracle, frame
rng0 = np.random.default_rng(1)
for k in range(286):
    A = rng0.standard_normal((6, 6)); A *= rng0.random((6, 6)) < rng0.uniform(0.2, 0.8)
print(A)
Bk = BK(A); u, s, vt = np.linalg.svd(Bk)
print("skew svals", np.round(s,4))
K = skew_of(vt[2]); print("K moduli", np.round(np.linalg.svd(K,compute_uv=False),5))
Xs, F = comp_mats(K); V = np.array([L(A, X).ravel() for X in Xs])
print("oracle", np.sqrt(oracle(V,k=3)[0][0])/s[2])
# brute force: same-square comparators with kernel: also try T with blocks +-I on kernel plane (KT same anyway)
F_, w = frame(K); print("schur w", w)
# Lean-type rank-4 comparator: full search over SO(2)^3 rotations x torus  (rotations change frame only if moduli repeated)
best=0
rng=np.random.default_rng(0)
for t in range(20000):
    th = rng.uniform(0,2*np.pi,3)
    d = np.zeros(6); d[0::2]=np.cos(th); d[1::2]=np.sin(th)
    v = d@V; best=max(best, np.sqrt(v@v))
print("random search", best/s[2])
