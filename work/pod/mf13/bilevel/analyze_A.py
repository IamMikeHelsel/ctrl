import json, glob, sys
import numpy as np
from evalf import *
np.set_printoptions(precision=5, suppress=True, linewidth=170)
for fn in sorted(glob.glob('runs/A_*.best.json')):
    d = json.load(open(fn)); x = np.array(d['x'])
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    Y, err = Y_from_x(K, x[2:])
    out = f_of_pair(K, Y, tol=1e-11, want_z=True)
    A = out['A']
    print(fn)
    print("  eig(A):", np.sort_complex(np.linalg.eigvals(A)))
    print("  eig(sym A):", np.linalg.eigvalsh((A + A.T) / 2), " sv(A):", np.linalg.svd(A, compute_uv=False))
    print("  tr A", np.trace(A), "; K:", np.sort(w)[::-1])
    # sym top singular vectors
    u, s, vt = np.linalg.svd(BS(A))
    Sb, Kb = bases(6)
    print("  #sym sv>0.9999:", (s > 0.9999).sum())
    for j in range(min(3, (s > 0.999999).sum())):
        X = np.tensordot(vt[j], Sb, axes=(0, 0))
        print("   top right sym sv vec", j, "eig(X)=", np.linalg.eigvalsh(X), " <X,K^2>=", np.sum(X * (K @ K)))
