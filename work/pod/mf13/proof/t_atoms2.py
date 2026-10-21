import warnings; warnings.filterwarnings('ignore')
import sys, numpy as np, json
from core import *
from atoms2 import N4_bundle
from e07_dual_at import top_pair
rng = np.random.default_rng(5)
cases = []
for t in range(2):
    K = skew_of(rng.standard_normal(15)); Y = skew_of(rng.standard_normal(15)); cases.append((f"random{t}", K, Y))
for t in range(3):
    K, Y, _ = top_pair(rng.standard_normal((6, 6))); cases.append((f"natural{t}", K, Y))
K, Y, _ = top_pair(np.load('logs/e05_n6_s1_e0.05_best.npy')); cases.append(("SSfail", K, Y))
only = sys.argv[1:]
for name, K, Y in cases:
    if only and name not in only: continue
    print("case", name, flush=True)
    K = K / np.linalg.norm(K); Y = Y / np.linalg.norm(Y); P = Y @ K
    Nv, ub, lbh, hist = N4_bundle(P, rng, iters=60, verbose=True)
    print(json.dumps(dict(case=name, N=Nv, N4_upper_rigorous=ub, N4_lower_heuristic=lbh, its=len(hist))), flush=True)
