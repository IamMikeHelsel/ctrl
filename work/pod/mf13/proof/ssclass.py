"""Fast evaluation of the pointwise same-square (Chen-Tian) class value
   g_K(K,Y) = min_z max_{T in T(K)} ||L_{A(z)}(K T)|| / ||K||
where T(K) = { F diag(R(th1),R(th2),R(th3)) F^T } (symmetric involutions anticommuting with K; all of them when the
three moduli of K are distinct).  Also returns the optimal measure nu on the torus (SOCP dual weights).
L_{A(z)}(KT) = sum_j d_j v_j(z), d = (cos th1, sin th1, cos th2, ...), so ||.||^2 = d^T G(z) d."""
import numpy as np
import cvxpy as cp
from scipy.linalg import schur
from scipy.optimize import minimize
from core import *

R0 = np.diag([1., -1.]); R1 = np.array([[0., 1.], [1., 0.]])


def frame(X):
    """orthonormal F with F^T X F = diag(w_i J) (robust for singular / repeated moduli)."""
    n = X.shape[0]
    F = np.zeros((n, n)); w = np.zeros(n // 2)
    Q = np.eye(n)                      # orthonormal basis of the remaining invariant subspace
    for i in range(n // 2):
        Xr = Q.T @ X @ Q
        ev, U = np.linalg.eigh(-Xr @ Xr)
        v1 = Q @ U[:, -1]
        v2 = X @ v1; nv = np.linalg.norm(v2)
        if nv < 1e-12 * max(1, np.linalg.norm(X)):
            v2 = Q @ U[:, -2]; nv = 0.0
        else:
            v2 = v2 / nv
        F[:, 2 * i] = v1; F[:, 2 * i + 1] = -v2 if nv > 0 else v2
        w[i] = nv
        P = np.eye(n) - np.outer(v1, v1) - np.outer(v2, v2)
        u_, s_, _ = np.linalg.svd(P @ Q)
        Q = u_[:, :n - 2 * (i + 1)]
    return F, w


def comp_mats(K):
    """6 symmetric matrices X_j = K F diag(..R0/R1 in block i..) F^T  (KT = sum_j d_j X_j)."""
    F, w = frame(K)
    n = K.shape[0]
    Xs = []
    for i in range(n // 2):
        for R in (R0, R1):
            M = np.zeros((n, n)); M[2*i:2*i+2, 2*i:2*i+2] = R
            Xs.append(K @ F @ M @ F.T)
    return np.array(Xs), F


def Tmat(F, th):
    n = F.shape[0]; T0 = np.zeros((n, n))
    for i in range(len(th)):
        T0[2*i:2*i+2, 2*i:2*i+2] = np.cos(th[i]) * R0 + np.sin(th[i]) * R1
    return F @ T0 @ F.T


def dvec(th):
    th = np.atleast_2d(th)
    d = np.zeros((th.shape[0], 2 * th.shape[1]))
    d[:, 0::2] = np.cos(th); d[:, 1::2] = np.sin(th)
    return d


_GRID = None


def grid(ng=18):
    global _GRID
    if _GRID is None or _GRID[0] != ng:
        t = np.linspace(0, 2 * np.pi, ng, endpoint=False)
        g = np.stack(np.meshgrid(t, t, t, indexing='ij'), -1).reshape(-1, 3)
        _GRID = (ng, g, dvec(g))
    return _GRID[1], _GRID[2]


def ss_setup(K, A0, Ar, side='K'):
    """returns V0 (6,m) and Vr (r,6,m): L_{A(z)}(X_j) flattened, normalised by ||K||."""
    Xs, F = comp_mats(K)
    nk = np.linalg.norm(K)
    V0 = np.array([L(A0, X).ravel() for X in Xs]) / nk
    Vr = np.array([[L(Ai, X).ravel() for X in Xs] for Ai in Ar]) / nk
    return V0, Vr, F


def oracle(Vz, k=6):
    g, D = grid()
    vals = np.sum((D @ Vz) ** 2, axis=1)
    idx = np.argsort(-vals)[:k * 3]
    out = []
    for i in idx:
        def neg(th):
            d = dvec(th)[0]; v = d @ Vz
            return -v @ v
        r = minimize(neg, g[i], method='BFGS', options=dict(gtol=1e-12))
        th = np.mod(r.x, 2 * np.pi)
        if all(np.linalg.norm(np.angle(np.exp(1j * (th - o[1])))) > 1e-4 for o in out):
            out.append((-r.fun, th))
        if len(out) >= k: break
    out.sort(key=lambda o: -o[0])
    return out


def g_K(K, Y, A0=None, Ar=None, tol=1e-10, maxit=200, return_all=False, verbose=False):
    if A0 is None:
        A0, Ar, res = affine_family(K, Y)
    V0, Vr, F = ss_setup(K, A0, Ar)
    r = len(Vr)
    g, D = grid()
    # initial cuts: coarse grid points with largest value at z=0
    cuts = [o[1] for o in oracle(V0, k=8)]
    cuts += list(g[np.random.default_rng(0).choice(len(g), 30, replace=False)])
    z = np.zeros(r)
    for it in range(maxit):
        Dc = dvec(np.array(cuts))
        zv = cp.Variable(r); t = cp.Variable()
        # rows: d^T (V0 + sum z Vr)
        C0 = Dc @ V0                                  # (nc, m)
        Cr = np.einsum('cj,rjm->rcm', Dc, Vr)         # (r, nc, m)
        cons = [cp.norm(C0[c] + Cr[:, c, :].T @ zv) <= t for c in range(len(cuts))]
        prob = cp.Problem(cp.Minimize(t), cons)
        prob.solve(solver=cp.CLARABEL)
        lo = t.value; z = zv.value
        Vz = V0 + np.tensordot(z, Vr, axes=(0, 0))
        orc = oracle(Vz)
        hi = np.sqrt(orc[0][0])
        if verbose: print(it, len(cuts), lo, hi)
        if hi - lo < tol * max(1, hi):
            break
        for val, th in orc:
            if np.sqrt(val) > lo + 0.1 * (hi - lo):
                cuts.append(th)
    if return_all:
        lam = np.array([c.dual_value for c in cons]).ravel()
        keep = lam > 1e-8 * lam.max()
        return dict(lo=lo, hi=hi, z=z, nu_th=np.array(cuts)[keep], nu_w=lam[keep] / lam[keep].sum(), F=F,
                    A=A0 + np.tensordot(z, Ar, axes=(0, 0)), it=it)
    return lo, hi
