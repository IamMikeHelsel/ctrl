"""At a CMA ridge point: recover angles of Xv, Xu; compute local dimension of the solution set of
   {moments=0, Xu Xv in Range(M^T)} in the variables (y in R^15, theta, phi) with K fixed, and with a,b,c free."""
import json, glob, sys
import numpy as np
from scipy.optimize import least_squares
from ridge_solve import Xs, resid, Kb
from evalf import *
np.set_printoptions(precision=4, suppress=True, linewidth=160)
Sb, Kb_ = bases(6)

def Xof(v): return np.tensordot(v, Sb, axes=(0, 0))
for fn in sorted(glob.glob('runs/A_*.best.json'))[:3]:
    d = json.load(open(fn)); x = np.array(d['x'])
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    Y, err = Y_from_x(K, x[2:])
    out = f_of_pair(K, Y, tol=1e-12, want_z=True)
    u, s, vt = np.linalg.svd(BS(out['A']))
    Xv = Xof(vt[0]); Xu = Xof(u[:, 0])
    # recover angles: block (i,i) of Xv = w_i R(theta): R=[[cos, sin],[sin,-cos]]
    wK = np.array([K[0, 1], K[2, 3], K[4, 5]])
    th = np.array([np.arctan2(Xv[2*i, 2*i+1] / wK[i], Xv[2*i, 2*i] / wK[i]) for i in range(3)])
    from fss import canon_frame
    FY, wY = canon_frame(Y)
    Xu_c = FY.T @ Xu @ FY
    ph = np.array([np.arctan2(Xu_c[2*i, 2*i+1] / wY[i], Xu_c[2*i, 2*i] / wY[i]) for i in range(3)])
    Xu2, Xv2 = Xs(K, Y, th, ph)
    print(fn, "recon err Xv", min(np.linalg.norm(Xv2 - Xv), np.linalg.norm(Xv2 + Xv)), "Xu", min(np.linalg.norm(Xu2 - Xu), np.linalg.norm(Xu2 + Xu)))
    # sign fix
    if np.linalg.norm(Xv2 + Xv) < np.linalg.norm(Xv2 - Xv): th = th + np.pi
    if np.linalg.norm(Xu2 + Xu) < np.linalg.norm(Xu2 - Xu): ph = ph + np.pi
    x0 = np.concatenate([vec_from_skew(Y), th, ph])
    r0 = resid(x0, K)
    print("   residual at ridge point:", np.linalg.norm(r0))
    # Jacobian
    h = 1e-6
    Jm = np.array([(resid(x0 + h * e, K) - resid(x0 - h * e, K)) / (2 * h) for e in np.eye(21)]).T
    sv = np.linalg.svd(Jm, compute_uv=False)
    print("   Jacobian sv (21 vars):", sv)
    print("   local solution-set dim (K fixed):", (sv < 1e-6).sum())
