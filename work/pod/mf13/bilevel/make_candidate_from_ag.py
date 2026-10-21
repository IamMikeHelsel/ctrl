"""usage: make_candidate_from_ag.py BEST.json N OUT.json
Rebuild (K,Y) from a Track-A-generic best point, solve the inner problem to 1e-13, and store A* (40 digits)."""
import sys, json
import numpy as np
import mpmath as mp
fn, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
sys.argv = ['x', str(n), '1', '0.02', '1']
import track_a_gen as T
from bl import *
from barrier import barrier_min_sigma
d = json.load(open(fn)); x = np.array(d['x'])
K, Y, err = T.build(x)
A0, Ar, resid, rank = affine_family(K, Y)
B0 = BS(A0); Br = np.array([BS(a) for a in Ar])
fv, z, t, nit = barrier_min_sigma(B0, Br, tol=1e-13)
A = A0 + np.tensordot(z, Ar, axes=(0, 0))
s, k = norms(A)
print("double precision: sym", s, "skew", k, "gap", k - s, " pair residual", np.linalg.norm(A @ K + K @ A.T - Y))
mp.mp.dps = 50
json.dump(dict(note=f'n={n} strict counterexample found by bilevel Track A (generic n) CMA from random start; A is the double-precision inner optimum, stored exactly as the 40-digit decimal expansion of the float64 entries; verify with verify_candidate.py',
               n=n, f_double=float(fv), x_outer=x.tolist(), A=[[mp.nstr(mp.mpf(float(v)), 40) for v in row] for row in A]), open(out, 'w'), indent=1)
