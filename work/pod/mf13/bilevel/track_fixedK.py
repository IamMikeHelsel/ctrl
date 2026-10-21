"""Fixed K shape (a:b:c), CMA over Y only (15 raw vars), many restarts. usage: track_fixedK.py A B C NRESTARTS GENS SEED"""
import sys, json, time
import numpy as np, cma
from evalf import *
a, b, c = [float(v) for v in sys.argv[1:4]]
nre = int(sys.argv[4]); gens = int(sys.argv[5]); seed = int(sys.argv[6])
w = np.array([a, b, c]); w = w / np.linalg.norm(w) / np.sqrt(2)
K = make_K(*w)
rng = np.random.default_rng(seed)
res = []
def obj(y):
    Y, err = Y_from_x(K, y)
    if Y is None or err > 1e-10: return 50.0
    sY = np.linalg.svd(Y, compute_uv=False)[-1]
    out = f_of_pair(K, Y, tol=1e-9)
    if not np.isfinite(out['f']) or out['kept_sv'] < 1e-7: return 50.0
    return out['f'] + 50 * max(0, 0.02 - sY)
t0 = time.time()
tag = f"fixedK_{a}_{b}_{c}_s{seed}"
for r in range(nre):
    y0 = rng.standard_normal(15)
    es = cma.CMAEvolutionStrategy(y0, 0.7, dict(popsize=16, seed=int(rng.integers(1e6)), verbose=-9, maxiter=gens, tolfun=1e-12))
    best = np.inf
    while not es.stop():
        xs = es.ask(); fs = [obj(x) for x in xs]; es.tell(xs, fs); best = min(best, min(fs))
    res.append(best)
    print(f"restart {r}: best f={best:.10f}  (min so far {min(res):.10f}) t={time.time()-t0:.0f}s", flush=True)
json.dump(dict(w=w.tolist(), res=res), open(f'runs/{tag}.json', 'w'))
