import json, glob
import numpy as np
from evalf import *
from scipy.linalg import expm
import mpmath as mp
np.set_printoptions(precision=5, suppress=True, linewidth=170)
rows = []
for fn in sorted(glob.glob('runs/A_*.best.json')) + sorted(glob.glob('runs/B_*.best.json')):
    d = json.load(open(fn)); x = np.array(d['x']); tag = fn.split('/')[-1].replace('.best.json', '')
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    if tag.startswith('A_'):
        Y, err = Y_from_x(K, x[2:])
    else:
        kind = tag.split('_')[1]
        U = expm(skew_from_vec(x[2:17])); Jb = np.kron(np.eye(3), J2)
        Q = U @ Jb @ U.T if kind == 'J' else U @ np.diag([-1.]*int(kind) + [1.]*(6-int(kind))) @ U.T
        Y = Q @ K @ Q.T
    out = f_of_pair(K, Y, tol=1e-12, want_z=True)
    s, k = norms(out['A'])
    ev = np.linalg.eigvals(Y @ K); ev = np.sort_complex(ev)[::2]
    sK = np.sort(np.linalg.svd(K, compute_uv=False)[::2])[::-1]; sY = np.sort(np.linalg.svd(Y, compute_uv=False)[::2])[::-1]
    print(f"{tag:22s} f-1={out['f']-1: .2e}  s(A*)-1={s-1: .1e} k(A*)-1={k-1: .1e}  sK={sK} sY={sY}  eig(YK)={np.round(ev,4)} nullity={out['nullity']}")
    rows.append(tag)
# n=6 reference ridge A (not a counterexample): save with 40 digits
d = json.load(open('runs/A_s2_e0.05.best.json')); x = np.array(d['x'])
w = abc_from_uv(x[0], x[1]); K = make_K(*w); Y, err = Y_from_x(K, x[2:])
out = f_of_pair(K, Y, tol=1e-13, want_z=True)
mp.mp.dps = 50
json.dump(dict(note='n=6 equality-ridge point (A* from Track A, eps=0.05, seed 2): s=k=1 to ~1e-10; NOT a counterexample', n=6,
               A=[[mp.nstr(mp.mpf(float(v)), 40) for v in row] for row in out['A']]), open('candidates/n6_ridge_reference_A.json', 'w'), indent=1)
