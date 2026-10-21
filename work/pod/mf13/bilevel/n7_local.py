"""Positive control: start Track-A-generic CMA (n=7) from the paper's pair (canonicalised), perturbed by relative scale PERT.
usage: n7_local.py PERT SEED MAXGEN"""
import sys, json, time
import numpy as np, cma
from scipy.linalg import schur
pert = float(sys.argv[1]); SIG0 = float(sys.argv[4]) if len(sys.argv) > 4 else 0.01; seed = int(sys.argv[2]); maxgen = int(sys.argv[3])
sys.argv = ['x', '7', str(seed), '0.02', '1']
import track_a_gen as T
from bl import *

A7 = np.array([[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[6,-5,-13,0,0,0,0],[-14,-18,0,0,0,0,0],[12,-12,11,0,0,0,0],[0,0,0,-6,0,-14,0],[0,0,0,6,-18,0,0]], float)
sig, K0, Y0, sv = skew_top_pair(A7)
# canonical frame of K0: real Schur, order blocks by |x| desc, kernel last
Tm, Z = schur(K0, output='real')
blocks = []
i = 0
while i < 7:
    if i + 1 < 7 and abs(Tm[i, i+1]) > 1e-9:
        blocks.append((abs(Tm[i, i+1]), i, Tm[i, i+1])); i += 2
    else:
        kern = i; i += 1
blocks.sort(key=lambda b: -b[0])
cols = []; 
for xval, i0, sgn in blocks:
    e1 = Z[:, i0]; e2 = Z[:, i0+1]
    if sgn < 0: e1, e2 = e2, e1   # make K block = +x J  (J=[[0,1],[-1,0]]: K e2 = -x e1... fix by test)
    cols += [e1, e2]
cols.append(Z[:, kern])
Q = np.array(cols).T
Kc = Q.T @ K0 @ Q
print("Kc block structure:\n", np.round(Kc, 4))
# fix block signs so that Kc[0,1]>0 etc.
for b in range(3):
    if Kc[2*b, 2*b+1] < 0:
        Q[:, 2*b:2*b+2] = Q[:, [2*b+1, 2*b]]
Kc = Q.T @ K0 @ Q
Yc = Q.T @ Y0 @ Q
a, b, c = Kc[0, 1], Kc[2, 3], Kc[4, 5]
print("abc", a, b, c, " |K - make_K|", np.linalg.norm(Kc - T.make_K(a, b, c)))
x0 = np.concatenate([[np.log(b / a), np.log(c / a)], np.array([np.sum(Yc * B) for B in T.Kb])])
o0, info = T.objective(x0, full=True)
print("objective at canonical paper pair:", o0, "f", info['f'] if info else None)
rng = np.random.default_rng(seed)
xs0 = x0 + pert * rng.standard_normal(len(x0)) * np.linalg.norm(x0) / np.sqrt(len(x0))
print("objective at perturbed start:", T.objective(xs0))
es = cma.CMAEvolutionStrategy(xs0, SIG0, dict(popsize=16, seed=seed + 1, verbose=-9, maxiter=maxgen, tolfun=1e-13))
best = (np.inf, None); t0 = time.time(); gen = 0
while not es.stop():
    xs = es.ask(); fs = [T.objective(x) for x in xs]; es.tell(xs, fs); gen += 1
    if min(fs) < best[0]: best = (min(fs), xs[int(np.argmin(fs))])
    if gen % 5 == 0: print(f"gen {gen} best {best[0]:.8f} t={time.time()-t0:.0f}s", flush=True)
o, info = T.objective(best[1], full=True)
print("FINAL best f", info['f'], " sym/skew norms of A*:", norms(info['A']), "nullity", info['nullity'])
json.dump(dict(f=info['f'], x=best[1].tolist(), A=info['A'].tolist(), K=info['K'].tolist(), Y=info['Y'].tolist()), open(f'runs/n7_local_{pert}_{seed}.json', 'w'))
