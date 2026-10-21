"""E03: sample g_K (pointwise same-square class, K side) on many compatible pairs.
mode gauss: K random canonical, Y gaussian projected.  mode nat: (K,Y) = top skew pair of a random A."""
import sys, json
import numpy as np
from core import *
from e02_ss_minimax import g_value

seed = int(sys.argv[1]); N = int(sys.argv[2]); mode = sys.argv[3]
rng = np.random.default_rng(seed)
out = []
for k in range(N):
    if mode == 'gauss':
        K, Y, err = random_pair(rng)
    else:
        A = rng.standard_normal((6, 6))
        if mode == 'natsparse':
            A *= rng.random((6, 6)) < 0.5
        Bk = BK(A); u, s, vt = np.linalg.svd(Bk)
        K = skew_of(vt[0]); Y = skew_of(u[:, 0])
    sK = np.linalg.svd(K, compute_uv=False)[::2]
    f, Aopt, info = inner_barrier(K, Y)
    gK = g_value(K, Y, ('K',), seed=k)
    rec = dict(k=k, f=f, gK=float(gK[1]), gKlo=float(gK[0]), sK=sK.tolist(), nullity=len(info['Ar']))
    out.append(rec)
    print(json.dumps(rec), flush=True)
