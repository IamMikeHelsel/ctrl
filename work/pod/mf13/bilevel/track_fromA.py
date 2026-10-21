"""CMA-ES over A (n^2 dims, generic n): objective f(top skew pair of A) = min over the affine family of the sym norm,
(with sigma normalised to 1). f<1 => strict counterexample (the family's A* has sym norm f < 1 <= skew norm).
Also records plain ratio s(A)/k(A).  usage: track_fromA.py SEED N MAXGEN [POP] [SIGMA0] [STRUCT]
STRUCT in {none, blk33, blk24, blk222, cplx}: restrict A to a structured class (to probe degenerate strata)."""
import sys, json, time, os
import numpy as np, cma
from bl import *
from barrier import barrier_min_sigma

seed = int(sys.argv[1]); n = int(sys.argv[2]); maxgen = int(sys.argv[3])
pop = int(sys.argv[4]) if len(sys.argv) > 4 else 24
sigma0 = float(sys.argv[5]) if len(sys.argv) > 5 else 0.5
struct = sys.argv[6] if len(sys.argv) > 6 else 'none'
tag = f"FA_n{n}_s{seed}_{struct}"
os.makedirs('runs', exist_ok=True)
logf = open(f'runs/{tag}.log', 'a')


def mask_for(struct, n):
    M = np.ones((n, n))
    def blocks(sizes):
        M = np.zeros((n, n)); o = 0
        for s in sizes: M[o:o+s, o:o+s] = 1; o += s
        return M
    if struct == 'blk33': return blocks([3, 3])
    if struct == 'blk24': return blocks([2, 4])
    if struct == 'blk222': return blocks([2, 2, 2])
    if struct == 'blk51': return blocks([5, 1])
    return M


MASK = mask_for(struct, n)


def f_from_A(A, tol=1e-9, full=False):
    sig, K, Y, sv = skew_top_pair(A)
    if sig < 1e-9: return 50.0
    gap = (sv[0] - sv[1]) / sv[0]
    A0, Ar, resid, rank = affine_family(K, Y)
    if resid > 1e-7: return 50.0
    B0 = BS(A0); Br = np.array([BS(a) for a in Ar])
    fv, z, t, nit = barrier_min_sigma(B0, Br, tol=tol)
    if full:
        return fv, dict(K=K, Y=Y, nullity=len(Ar), sv=sv[:4], z=z, A=A0 + np.tensordot(z, Ar, axes=(0, 0)))
    return fv


def obj(x):
    A = (x.reshape(n, n)) * MASK
    if np.linalg.norm(A) < 1e-9: return 50.0
    return f_from_A(A)


rng = np.random.default_rng(seed)
x0 = rng.standard_normal(n * n)
es = cma.CMAEvolutionStrategy(x0, sigma0, dict(popsize=pop, seed=seed + 1, verbose=-9, maxiter=maxgen, tolfun=1e-13, tolx=1e-13))
best = dict(obj=np.inf); t0 = time.time(); gen = 0
while not es.stop():
    xs = es.ask(); fs = [obj(x) for x in xs]; es.tell(xs, fs); gen += 1
    i = int(np.argmin(fs))
    if fs[i] < best['obj']: best = dict(obj=fs[i], x=xs[i].tolist())
    if gen % 10 == 0:
        print(f"gen {gen} best f={best['obj']:.10f} sigma={es.sigma:.3e} t={time.time()-t0:.0f}s", file=logf, flush=True)
        json.dump(best, open(f'runs/{tag}.best.json', 'w'))
fv, info = f_from_A((np.array(best['x']).reshape(n, n)) * MASK, tol=1e-12, full=True)
json.dump(dict(best, f=fv, nullity=info['nullity'], sv=info['sv'].tolist()), open(f'runs/{tag}.final.json', 'w'))
print("DONE", fv, "nullity", info['nullity'], file=logf, flush=True)
