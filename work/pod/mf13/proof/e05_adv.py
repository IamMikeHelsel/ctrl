"""E05: adversarial search for SS6 at the TOP skew pair:
   minimise rho(A) = max_{T in T(K_A)} ||L_A(K_A T)|| / k(A)   over A in R^{n x n}  (CMA-ES)
Also reports sigma_min(K_A) (rank-4 ridge => rho>=1 by the Lean theorem) and s(A)/k(A).
n=7 positive control: same objective (T acts on kernel by +-1); KV example has rho<1 (same-square fails)."""
import sys, json, warnings
warnings.filterwarnings('ignore')
import numpy as np
import cma
from core import *
from ssclass import comp_mats, oracle

n = int(sys.argv[1]); seed = int(sys.argv[2]); gens = int(sys.argv[3])
sig0 = float(sys.argv[4]) if len(sys.argv) > 4 else 0.3
eps = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0


def rho(A, full=False):
    Bk = BK(A); u, s, vt = np.linalg.svd(Bk)
    K = skew_of(vt[0], n)
    Xs, F = comp_mats(K)
    V = np.array([L(A, X).ravel() for X in Xs])
    if n % 2 == 1:
        pass  # comp_mats handles the kernel: T=+-1 on kernel line gives KT unchanged
    best = oracle(V, k=1)[0][0]
    r = np.sqrt(best) / s[0]
    sk = np.linalg.svd(K, compute_uv=False)
    pen = 10 * max(0.0, eps - sk[n - 1 - (n % 2)]) if eps > 0 else 0.0
    if full:
        return r, sk, np.linalg.norm(BS(A), 2) / s[0], s
    return r + pen


rng = np.random.default_rng(seed)
x0 = rng.standard_normal(n * n); x0 /= np.linalg.norm(x0)
best = (np.inf, None)
es = cma.CMAEvolutionStrategy(x0, sig0, dict(seed=seed, verbose=-9, popsize=16))
for g in range(gens):
    X = es.ask()
    F = [rho(np.array(x).reshape(n, n) / np.linalg.norm(x)) for x in X]
    es.tell(X, F)
    i = int(np.argmin(F))
    if F[i] < best[0]:
        best = (F[i], np.array(X[i]).reshape(n, n) / np.linalg.norm(X[i]))
    if g % 20 == 0 or g == gens - 1:
        r, sk, sr, s = rho(best[1], full=True)
        print(json.dumps(dict(g=g, rho=r, sK=np.round(sk[::2], 5).tolist(), s_over_k=sr, k2=s[1] / s[0])), flush=True)
np.save(f'logs/e05_n{n}_s{seed}_e{eps}_best.npy', best[1])
