"""Generic-n Track A (positive control for n=7):  K = diag(aJ,bJ,cJ,0..), Y in K_n projected onto the compatibility set
(least-squares solvability of the pair equations, Gauss-Newton on the unsolvable residual), then inner convex min.
usage: track_a_gen.py N SEED EPS MAXGEN [POP] [SIGMA0] [x0json]"""
import sys, json, time, os
import numpy as np, cma
from bl import *
from barrier import barrier_min_sigma

n = int(sys.argv[1]); seed = int(sys.argv[2]); eps = float(sys.argv[3]); maxgen = int(sys.argv[4])
pop = int(sys.argv[5]) if len(sys.argv) > 5 else 24
sigma0 = float(sys.argv[6]) if len(sys.argv) > 6 else 0.5
Sb, Kb = bases(n)
m = len(Kb)
tag = f"AG_n{n}_s{seed}_e{eps}"
os.makedirs('runs', exist_ok=True)
logf = open(f'runs/{tag}.log', 'a')
MU = 50.0


def make_K(a, b, c):
    K = np.zeros((n, n))
    K[0:2, 0:2] = a * J2; K[2:4, 2:4] = b * J2; K[4:6, 4:6] = c * J2
    return K


def skew_from_vec(y): return np.tensordot(y, Kb, axes=(0, 0))


def resid_vec(K, Y):
    M, rhs = pair_matrix_fast(K, Y)
    u, s, vt = np.linalg.svd(M, full_matrices=True)
    r = int((s > 1e-9 * s[0]).sum())
    Uc = u[:, r:]
    return np.concatenate([Uc @ (Uc.T @ rhs), [np.sum(Y * Y) - 1.0]])


def project(K, y, iters=40):
    for it in range(iters):
        Y = skew_from_vec(y)
        r = resid_vec(K, Y)
        if np.linalg.norm(r) < 1e-13: return y, np.linalg.norm(r)
        h = 1e-7
        J = np.array([(resid_vec(K, skew_from_vec(y + h * e)) - r) / h for e in np.eye(len(y))]).T
        dy = np.linalg.lstsq(J, -r, rcond=1e-10)[0]
        nd = np.linalg.norm(dy)
        if nd > 0.3: dy *= 0.3 / nd
        y = y + dy
    return y, np.linalg.norm(resid_vec(K, skew_from_vec(y)))


def abc_from_uv(u, v):
    w = np.array([1.0, np.exp(u), np.exp(v)]); return w / np.linalg.norm(w) / np.sqrt(2)


def build(x):
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    y0 = x[2:]; nrm = np.linalg.norm(y0)
    if nrm < 1e-9: return K, None, 1e9
    y, err = project(K, y0 / nrm)
    return K, skew_from_vec(y), err


def objective(x, full=False):
    K, Y, err = build(x)
    if Y is None or err > 1e-10: return (50.0, None) if full else 50.0
    sK = np.linalg.svd(K, compute_uv=False)[5]; sY = np.linalg.svd(Y, compute_uv=False)[5]
    pen = MU * (max(0.0, eps - sK) + max(0.0, eps - sY))
    A0, Ar, resid, rank = affine_family(K, Y)
    if resid > 1e-8: return (50.0, None) if full else 50.0
    B0 = BS(A0); Br = np.array([BS(a) for a in Ar])
    fv, z, t, nit = barrier_min_sigma(B0, Br, tol=1e-9)
    if full: return fv + pen, dict(f=fv, sK=sK, sY=sY, nullity=len(Ar), z=z, A=A0 + np.tensordot(z, Ar, axes=(0, 0)), K=K, Y=Y)
    return fv + pen


if __name__ == '__main__':
    rng = np.random.default_rng(seed)
    x0 = rng.standard_normal(2 + m)
    if len(sys.argv) > 7: x0 = np.array(json.load(open(sys.argv[7]))['x'])
    es = cma.CMAEvolutionStrategy(x0, sigma0, dict(popsize=pop, seed=seed + 1, verbose=-9, maxiter=maxgen, tolfun=1e-13, tolx=1e-13))
    best = dict(obj=np.inf); t0 = time.time(); gen = 0
    while not es.stop():
        xs = es.ask(); fs = [objective(x) for x in xs]; es.tell(xs, fs); gen += 1
        i = int(np.argmin(fs))
        if fs[i] < best['obj']: best = dict(obj=fs[i], x=xs[i].tolist())
        if gen % 5 == 0:
            print(f"gen {gen} best obj {best['obj']:.10f} sigma={es.sigma:.3e} t={time.time()-t0:.0f}s", file=logf, flush=True)
            json.dump(best, open(f'runs/{tag}.best.json', 'w'))
    o, info = objective(np.array(best['x']), full=True)
    s, k = norms(info['A'])
    print("DONE obj", best['obj'], "f", info['f'], "sym", s, "skew", k, file=logf, flush=True)
    json.dump(dict(best, f=info['f'], A=info['A'].tolist(), K=info['K'].tolist(), Y=info['Y'].tolist()), open(f'runs/{tag}.final.json', 'w'))
