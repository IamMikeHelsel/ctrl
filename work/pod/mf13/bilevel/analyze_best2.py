import json, glob, sys
import numpy as np
from evalf import *
np.set_printoptions(precision=6, suppress=True, linewidth=150)
for fn in sorted(glob.glob('runs/A_*.best.json')):
    d = json.load(open(fn)); x = np.array(d['x'])
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    Y, err = Y_from_x(K, x[2:])
    out = f_of_pair(K, Y, tol=1e-11, want_z=True)
    A = out['A']
    s, k = norms(A)
    print(fn, "f", out['f'], "s(A*)", s, "k(A*)", k, "k-s", k - s)
    sv_s = np.linalg.svd(BS(A), compute_uv=False); sv_k = np.linalg.svd(BK(A), compute_uv=False)
    print("  top sym sv:", sv_s[:8]); print("  top skew sv:", sv_k[:8])
    print("  z*:", out['z'])
    print("  A*:\n", A)
