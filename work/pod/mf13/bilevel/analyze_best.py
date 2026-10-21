import json, glob, sys
import numpy as np
from evalf import *
np.set_printoptions(precision=5, suppress=True, linewidth=150)
for fn in sorted(glob.glob('runs/*.best.json')):
    d = json.load(open(fn)); x = np.array(d['x'])
    tag = fn.split('/')[-1]
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    if tag.startswith('A_'):
        Y, err = Y_from_x(K, x[2:])
    else:
        from scipy.linalg import expm
        kind = tag.split('_')[1]
        U = expm(skew_from_vec(x[2:17])); Jb = np.kron(np.eye(3), J2)
        Q = U @ Jb @ U.T if kind == 'J' else U @ np.diag([-1.]*int(kind) + [1.]*(6-int(kind))) @ U.T
        Y = Q @ K @ Q.T
    out = f_of_pair(K, Y)
    ev = np.linalg.eigvals(Y @ K)
    print(f"{tag}: f={out['f']:.10f} abc={np.sort(w)[::-1]}  |Y-K|={np.linalg.norm(Y-K):.4f} |Y+K|={np.linalg.norm(Y+K):.4f} <K,Y>={np.sum(K*Y):.4f}")
    print("    sv(Y)=", np.linalg.svd(Y, compute_uv=False)[::2], " eig(YK)=", np.sort_complex(ev)[::2])
