"""Ridge characterisation test: find compatible (K,Y) with anticommuting same-square comparators Xv in SS_R(K), Xu in SS_R(Y)
such that Xu Xv in Range(M^T) = {Z1 K + Y Z2}.  Then check value <Xu, L_A Xv> (A in family) and f(K,Y)."""
import sys
import numpy as np
from scipy.optimize import least_squares
import fss
fss.SMOOTH = True
from fss import block_basis, canon_frame
from evalf import *
from bl import pair_matrix_fast

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
Sb, Kb = bases(6)


def Xs(K, Y, th, ph):
    wK = np.array([K[0, 1], K[2, 3], K[4, 5]])
    mats, _ = block_basis(np.eye(6), np.abs(wK))
    Xv = sum((np.cos(th[i]) * mats[2*i] + np.sin(th[i]) * mats[2*i+1]) for i in range(3))
    FY, wY = canon_frame(Y)
    matsY, _ = block_basis(FY, wY)
    Xu = sum((np.cos(ph[i]) * matsY[2*i] + np.sin(ph[i]) * matsY[2*i+1]) for i in range(3))
    return Xu, Xv


def resid(x, K):
    y = x[:15]; th = x[15:18]; ph = x[18:21]
    Y = skew_from_vec(y)
    m = moments(K, Y)
    Xu, Xv = Xs(K, Y, th, ph)
    P = Xu @ Xv
    # range of M^T = {Z1 K + Y Z2}
    cols = [(B @ K).ravel() for B in Kb] + [(Y @ B).ravel() for B in Kb]
    Mat = np.array(cols).T
    q, r_ = np.linalg.qr(Mat)   # may be rank deficient (rank 27 expected), use SVD
    u, s, vt = np.linalg.svd(Mat, full_matrices=False)
    U = u[:, s > 1e-9 * s[0]]
    p = P.ravel()
    res = p - U @ (U.T @ p)
    return np.concatenate([m, res])


if __name__ == '__main__':
    found = 0
    for trial in range(12):
        w = rng.uniform(0.1, 1, 3); w = w / np.linalg.norm(w) / np.sqrt(2)
        K = make_K(*w)
        y0 = rng.standard_normal(15); y0 /= np.linalg.norm(y0)
        y0, e, _ = project_Y(K, y0)
        x0 = np.concatenate([y0, rng.uniform(0, 2*np.pi, 6)])
        r = least_squares(resid, x0, args=(K,), xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=300)
        print(trial, 'res', np.linalg.norm(r.fun), 'nfev', r.nfev, 'norm Y', np.linalg.norm(r.x[:15]))
        if np.linalg.norm(r.fun) > 1e-9: continue
        Y = skew_from_vec(r.x[:15])
        if abs(np.linalg.norm(Y) - 1) > 1e-8: continue
        sYmin = np.linalg.svd(Y, compute_uv=False)[-1]
        out = f_of_pair(K, Y, tol=1e-11, want_z=True)
        Xu, Xv = Xs(K, Y, r.x[15:18], r.x[18:21])
        A0 = out['A0']
        val = np.sum(Xu * (A0 @ Xv + Xv @ A0.T))
        found += 1
        print(f"trial {trial}: |res|={np.linalg.norm(r.fun):.1e} sKmin={np.sort(w)[0]:.3f} sYmin={sYmin:.3f} value<Xu,L_A0 Xv>={val:.8f} |Xu|={np.linalg.norm(Xu):.4f} |Xv|={np.linalg.norm(Xv):.4f}  f={out['f']:.8f}")
    print("found", found)
