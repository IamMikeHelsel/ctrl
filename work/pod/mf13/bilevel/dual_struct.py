"""Inspect optimal dual certificate W (21x21) of the inner problem at a pair."""
import sys
import numpy as np
from evalf import *
np.set_printoptions(precision=4, suppress=True, linewidth=170)
Sb, Kb = bases(6)
def Xof(v): return np.tensordot(v, Sb, axes=(0, 0))
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
mode = sys.argv[2] if len(sys.argv) > 2 else 'gauss'
for trial in range(4):
    K, Y, err = random_pair(rng)
    out = f_of_pair(K, Y, tol=1e-12, want_z=True)
    A = out['A']; B = BS(A)
    t = out['f']
    G = t * t * np.eye(21) - B.T @ B
    W = B @ np.linalg.inv(G)
    # normalize nuclear norm 1
    u, s, vt = np.linalg.svd(W)
    s = s / s.sum()
    sv_B = np.linalg.svd(B, compute_uv=False)
    print(f"f={out['f']:.8f}; top sv of B*: {sv_B[:10]}")
    print("  dual weights p_i:", s[:10])
    # right/left singular vectors of W with weight
    for i in range(min(8, (s > 1e-3).sum())):
        Xv = Xof(vt[i]); Xu = Xof(u[:, i])
        eigv = np.linalg.eigvalsh(Xv)
        print(f"   i={i} p={s[i]:.4f}  Xv: |X^2+K^2|={np.linalg.norm(Xv@Xv+K@K):.3f} |XK+KX|={np.linalg.norm(Xv@K+K@Xv):.3f} eig={eigv}   Xu: |X^2+Y^2|={np.linalg.norm(Xu@Xu+Y@Y):.3f}")
    # verify dual value
    Wn = u @ np.diag(s) @ vt
    print("  <W, B*> =", np.sum(Wn * B) , " (should equal f)")
