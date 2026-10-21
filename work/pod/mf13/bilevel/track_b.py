"""Track B: Y = QKQ^T with Q^2 = +I symmetric orthogonal (k = number of -1 eigenvalues in {1,2,3}) or Q skew-orthogonal (Q^2=-I, kind 'J').
usage: track_b.py SEED KIND(1|2|3|J) EPS MAXGEN [POP] [SIGMA0]"""
import sys, json, time, os
import numpy as np, cma
from scipy.linalg import expm
from evalf import *

seed = int(sys.argv[1]); kind = sys.argv[2]; eps = float(sys.argv[3]); maxgen = int(sys.argv[4])
pop = int(sys.argv[5]) if len(sys.argv) > 5 else 16
sigma0 = float(sys.argv[6]) if len(sys.argv) > 6 else 0.5
tag = f"B_{kind}_s{seed}_e{eps}"
os.makedirs('runs', exist_ok=True)
logf = open(f'runs/{tag}.log', 'a')
MU = 50.0
Jb = np.kron(np.eye(3), J2)


def build(x):
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    G = skew_from_vec(x[2:17])
    U = expm(G)
    if kind == 'J':
        Q = U @ Jb @ U.T
    else:
        k = int(kind)
        Q = U @ np.diag([-1.] * k + [1.] * (6 - k)) @ U.T
    Y = Q @ K @ Q.T
    return K, Y


def objective(x, full=False):
    K, Y = build(x)
    sK = np.linalg.svd(K, compute_uv=False)[-1]
    pen = MU * max(0.0, eps - sK)
    out = f_of_pair(K, Y)
    if not np.isfinite(out['f']) or out['kept_sv'] < 1e-7:
        return (50.0, None) if full else 50.0
    obj = out['f'] + pen
    if full:
        out.update(sK=sK, sY=sK, pen=pen); return obj, out
    return obj


rng = np.random.default_rng(seed)
x0 = np.concatenate([rng.standard_normal(2) * 0.5, rng.standard_normal(15) * 0.7])
es = cma.CMAEvolutionStrategy(x0, sigma0, dict(popsize=pop, seed=seed + 1, verbose=-9, maxiter=maxgen, tolfun=1e-12, tolx=1e-12))
best = dict(obj=np.inf); t0 = time.time(); gen = 0
while not es.stop():
    xs = es.ask(); fs = [objective(x) for x in xs]; es.tell(xs, fs); gen += 1
    i = int(np.argmin(fs))
    if fs[i] < best['obj']: best = dict(obj=fs[i], x=xs[i].tolist())
    if gen % 10 == 0:
        obj, out = objective(np.array(best['x']), full=True)
        print(f"gen {gen} best obj {best['obj']:.8f} f={out['f']:.8f} sK={out['sK']:.4f} sigma={es.sigma:.3e} t={time.time()-t0:.0f}s", file=logf, flush=True)
        json.dump(best, open(f'runs/{tag}.best.json', 'w'))
K, Y = build(np.array(best['x']))
obj, out = objective(np.array(best['x']), full=True)
json.dump(dict(best, f=out['f'], K=K.tolist(), Y=Y.tolist(), desc=str(describe_pair(K, Y))), open(f'runs/{tag}.final.json', 'w'))
print("DONE", out['f'], file=logf, flush=True)
