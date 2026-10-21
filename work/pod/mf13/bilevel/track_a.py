"""Track A: CMA-ES over 17 outer variables (u,v for K; y in R^15 for Y raw, projected onto moment manifold).
Objective: f(K,Y) + penalty for small sv of K / Y (full-rank barrier eps).
usage: track_a.py SEED EPS MAXGEN [POP] [SIGMA0] [start]"""
import sys, json, time, os
import numpy as np, cma
from evalf import *

seed = int(sys.argv[1]); eps = float(sys.argv[2]); maxgen = int(sys.argv[3])
pop = int(sys.argv[4]) if len(sys.argv) > 4 else 16
sigma0 = float(sys.argv[5]) if len(sys.argv) > 5 else 0.5
tag = f"A_s{seed}_e{eps}"
os.makedirs('runs', exist_ok=True)
logf = open(f'runs/{tag}.log', 'a')
best = dict(obj=np.inf)
MU = 50.0


def build(x):
    w = abc_from_uv(x[0], x[1])
    K = make_K(*w)
    Y, err = Y_from_x(K, x[2:])
    return K, Y, err


def objective(x, full=False):
    K, Y, err = build(x)
    if Y is None or err > 1e-10:
        return (50.0, None) if full else 50.0
    sK = np.linalg.svd(K, compute_uv=False)[-1]; sY = np.linalg.svd(Y, compute_uv=False)[-1]
    pen = MU * (max(0.0, eps - sK) + max(0.0, eps - sY))
    out = f_of_pair(K, Y)
    if not np.isfinite(out['f']) or out['kept_sv'] < 1e-7:
        return (50.0, None) if full else 50.0
    obj = out['f'] + pen
    if full:
        out.update(sK=sK, sY=sY, pen=pen)
        return obj, out
    return obj


rng = np.random.default_rng(seed)
x0 = rng.standard_normal(17)
es = cma.CMAEvolutionStrategy(x0, sigma0, dict(popsize=pop, seed=seed + 1, verbose=-9, maxiter=maxgen, tolfun=1e-12, tolx=1e-12))
t0 = time.time()
gen = 0
while not es.stop():
    xs = es.ask()
    fs = [objective(x) for x in xs]
    es.tell(xs, fs)
    gen += 1
    i = int(np.argmin(fs))
    if fs[i] < best['obj']:
        best = dict(obj=fs[i], x=xs[i].tolist())
    if gen % 10 == 0:
        obj, out = objective(np.array(best['x']), full=True)
        msg = f"gen {gen} best obj {best['obj']:.8f}  f={out['f']:.8f} sK={out['sK']:.4f} sY={out['sY']:.4f} pen={out['pen']:.2e} sigma={es.sigma:.3e} t={time.time()-t0:.0f}s"
        print(msg, file=logf, flush=True)
        json.dump(best, open(f'runs/{tag}.best.json', 'w'))
obj, out = objective(np.array(best['x']), full=True)
K, Y, err = build(np.array(best['x']))
res = dict(best, f=out['f'], sK=float(out['sK']), sY=float(out['sY']), K=K.tolist(), Y=Y.tolist(), desc=str(describe_pair(K, Y)))
json.dump(res, open(f'runs/{tag}.final.json', 'w'))
print("DONE", res['f'], file=logf, flush=True)
