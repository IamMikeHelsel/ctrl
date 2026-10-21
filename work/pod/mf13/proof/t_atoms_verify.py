"""Negative test for the atomic certificate at the SS-fail pair:
run the bundle (saves center G with <G,P> = 1), then re-evaluate phi(G) = max over atoms <G,a> with a heavy oracle
(200 random starts per family + BFGS polish). If phi(G) < 1 robustly, then N4(P) >= 1/phi(G) > 1: YK is NOT a convex
combination of rank<=4 / common-T atoms with total weight <= 1, although N(YK) < 1."""
import warnings; warnings.filterwarnings('ignore')
import sys, numpy as np
from scipy.optimize import minimize
from core import *
from atoms import Atoms
from atoms2 import N4_bundle
from e07_dual_at import top_pair
case = sys.argv[1]
rng = np.random.default_rng(5)
if case == 'SSfail':
    K, Y, _ = top_pair(np.load('logs/e05_n6_s1_e0.05_best.npy'))
else:  # natural1 as in t_atoms2
    for t in range(2): skew_of(rng.standard_normal(15)); skew_of(rng.standard_normal(15))
    for t in range(2): K, Y, _ = top_pair(rng.standard_normal((6, 6)))
K = K / np.linalg.norm(K); Y = Y / np.linalg.norm(Y); P = Y @ K
Nv, ub, lbh, hist = N4_bundle(P, np.random.default_rng(9), iters=60)
G = np.load('logs/atoms2_center.npy')
print(f"{case}: N = {Nv:.6f}; bundle 1/phi = {lbh:.6f}; <G,P> = {np.sum(G*P):.6f}", flush=True)
At = Atoms(6); At.G = G; best = {}
r2 = np.random.default_rng(123)
for f in At.fam:
    vals = []
    for st in range(200):
        x0 = r2.standard_normal(15) * (0.5 + 2.5 * r2.random())
        obj = lambda x: -At.val(f, At.Q(x).T @ G @ At.Q(x))[0]
        r = minimize(obj, x0, method='BFGS', options=dict(maxiter=400, gtol=1e-9))
        vals.append(-r.fun)
    vals = np.sort(vals)
    best[f] = vals[-1]
    print(f"  family {f}: max <G,a> over 200 starts = {vals[-1]:.6f}  (top5 {np.round(vals[-5:],6)})", flush=True)
phi = max(best.values())
print(f"RESULT {case}: phi(G) = {phi:.6f}  =>  N4 >= {1/phi:.6f}  vs N = {Nv:.6f}")
