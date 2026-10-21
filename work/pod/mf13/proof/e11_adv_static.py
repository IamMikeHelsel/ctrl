"""E11: adversarial MAXIMISATION of N(YK) over unit skew K, Y (static form of Byers-Nash).
n=6: K = diag(aJ,bJ,cJ) canonical (2 params), Y raw (15); n=7: K = diag(aJ,bJ,cJ,0) (2 params), Y raw (21).
Conjecture_n <=> max N(YK) <= 1.  Barrier-free (rank-deficient K are allowed: then N<=1 is a theorem)."""
import sys, json, warnings
warnings.filterwarnings('ignore')
import numpy as np
import cma
from core import *
from staticN import N_of

n = int(sys.argv[1]); seed = int(sys.argv[2]); gens = int(sys.argv[3])
m = n * (n - 1) // 2

def pair(x):
    w = np.array([1.0, np.exp(x[0]), np.exp(x[1])]); w = w / np.linalg.norm(w) / np.sqrt(2)
    K = np.zeros((n, n)); K[:6, :6] = make_K(*w)
    Y = skew_of(x[2:2 + m], n); Y /= np.linalg.norm(Y)
    return K, Y

def obj(x):
    K, Y = pair(x)
    try:
        return -N_of(Y @ K)
    except Exception:
        return 0.0

rng = np.random.default_rng(seed)
x0 = np.concatenate([rng.normal(0, 0.5, 2), rng.standard_normal(m)])
es = cma.CMAEvolutionStrategy(x0, 0.5, dict(seed=seed, verbose=-9, popsize=14))
best = (np.inf, None)
for g in range(gens):
    X = es.ask(); F = [obj(np.array(x)) for x in X]; es.tell(X, F)
    i = int(np.argmin(F))
    if F[i] < best[0]: best = (F[i], np.array(X[i]))
    if g % 5 == 0 or g == gens - 1:
        K, Y = pair(best[1])
        print(json.dumps(dict(g=g, N=-best[0], mK=np.round(np.linalg.svd(K, compute_uv=False)[::2], 4).tolist(),
                              mY=np.round(np.linalg.svd(Y, compute_uv=False)[::2], 4).tolist())), flush=True)
        np.save(f'logs/e11_n{n}_s{seed}_best.npy', best[1])
