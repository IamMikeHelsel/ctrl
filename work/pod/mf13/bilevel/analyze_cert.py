import json, glob, sys
import numpy as np
from evalf import *
np.set_printoptions(precision=5, suppress=True, linewidth=170)
Sb, Kb = bases(6)
def Xof(v): return np.tensordot(v, Sb, axes=(0, 0))
for fn in sorted(glob.glob('runs/A_*.best.json')):
    d = json.load(open(fn)); x = np.array(d['x'])
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    Y, err = Y_from_x(K, x[2:])
    out = f_of_pair(K, Y, tol=1e-12, want_z=True)
    A = out['A']
    u, s, vt = np.linalg.svd(BS(A))
    Xv = Xof(vt[0]); Xu = Xof(u[:, 0])
    print(fn, "s0", s[0], "s1", s[1])
    print("  eig Xv", np.linalg.eigvalsh(Xv), "eig Xu", np.linalg.eigvalsh(Xu))
    print("  |Xu-Xv|", min(np.linalg.norm(Xu - Xv), np.linalg.norm(Xu + Xv)))
    for name, X in (('Xv', Xv), ('Xu', Xu)):
        print(f"  {name}: |X^2+K^2|={np.linalg.norm(X@X+K@K):.4f} |X^2+Y^2|={np.linalg.norm(X@X+Y@Y):.4f} |[X,K]|={np.linalg.norm(X@K-K@X):.4f} |[X,Y]|={np.linalg.norm(X@Y-Y@X):.4f} |XK+KX|={np.linalg.norm(X@K+K@X):.4f} |XY+YX|={np.linalg.norm(X@Y+Y@X):.4f}")
        print("     tr X", np.trace(X), " <X,KY+YK>", np.sum(X*(K@Y+Y@K)), " <X, K^2>", np.sum(X*(K@K)), " <X,Y^2>", np.sum(X*(Y@Y)))
    # check the product X_u X_v in range(M^T): residual of least squares  Xu Xv = Z1 K + Y Z2
    P = Xu @ Xv
    # solve for Z1,Z2 skew
    cols = []
    for Bk in Kb: cols.append((Bk @ K).ravel())
    for Bk in Kb: cols.append((Y @ Bk).ravel())
    Mat = np.array(cols).T
    co, res, rk, sv_ = np.linalg.lstsq(Mat, P.ravel(), rcond=None)
    print("  Xu Xv in span{Z1 K + Y Z2}: resid", np.linalg.norm(Mat @ co - P.ravel()), " rank", rk)
    print("  product Xu*Xv =\n", P)
