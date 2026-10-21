"""At ridge minimizers: X_v = K T_v, X_u = Y T_u ?  Is T_v = +-T_u (common anticommuting involution)?"""
import json, glob
import numpy as np
from evalf import *
np.set_printoptions(precision=4, suppress=True, linewidth=170)
Sb, Kb = bases(6)
for fn in sorted(glob.glob('runs/A_*.best.json')) + sorted(glob.glob('runs/B_*.best.json')):
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
    out = f_of_pair(K, Y, tol=1e-12, want_z=True)
    u, s, vt = np.linalg.svd(BS(out['A']))
    Xv = np.tensordot(vt[0], Sb, axes=(0, 0)); Xu = np.tensordot(u[:, 0], Sb, axes=(0, 0))
    Tv = np.linalg.solve(K, Xv); Tu = np.linalg.solve(Y, Xu)
    print(tag, f"f-1={out['f']-1:.1e}  s0={s[0]:.9f} s1={s[1]:.6f}")
    print(f"   Tv: sym={np.linalg.norm(Tv-Tv.T):.1e} orth={np.linalg.norm(Tv@Tv-np.eye(6)):.1e} anticomm K={np.linalg.norm(Tv@K+K@Tv):.1e} anticomm Y={np.linalg.norm(Tv@Y+Y@Tv):.1e}")
    print(f"   Tu: sym={np.linalg.norm(Tu-Tu.T):.1e} orth={np.linalg.norm(Tu@Tu-np.eye(6)):.1e} anticomm K={np.linalg.norm(Tu@K+K@Tu):.1e} anticomm Y={np.linalg.norm(Tu@Y+Y@Tu):.1e}")
    print(f"   |Tv-Tu|={min(np.linalg.norm(Tv-Tu), np.linalg.norm(Tv+Tu)):.2e}   spectrum Tv {np.round(np.linalg.eigvalsh((Tv+Tv.T)/2),3)}")
