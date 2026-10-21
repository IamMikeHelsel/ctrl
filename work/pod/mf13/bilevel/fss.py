"""f_ss(K,Y): restricted dual class. s(A) >= max_{Xu in SS_R(Y), Xv in SS_R(K)} <Xu, L_A Xv>, with SS_R(K) = { diag-block a_i R(theta_i) } (anticommuting same-square comparators).
f_ss = min_z of that max (convex; solved by cutting planes / LP).  f_ss <= f."""
import numpy as np
from scipy.optimize import linprog, minimize
from scipy.linalg import schur
from evalf import *

Sb6, Kb6 = bases(6)
SMOOTH = False
R0 = np.diag([1., -1.]); R1 = np.array([[0., 1.], [1., 0.]])


def block_basis(F, w):
    """6 symmetric matrices: for block i, w_i*(F E_i^c F^T), w_i*(F E_i^s F^T); coordinates in S-basis (21)."""
    mats = []
    for i in range(3):
        for R in (R0, R1):
            M = np.zeros((6, 6)); M[2*i:2*i+2, 2*i:2*i+2] = w[i] * R
            mats.append(F @ M @ F.T)
    mats = np.array(mats)
    coords = np.einsum('jab,iab->ji', mats, Sb6)   # (6,21)
    return mats, coords


_REF = np.random.default_rng(12345).standard_normal(6)


def canon_frame_smooth(Y):
    """deterministic smooth frame: eigenspaces of -Y^2 (sorted by eigenvalue desc); e1 = projection of fixed vector, e2 = Y e1 / |Y e1|."""
    ev, V = np.linalg.eigh(-Y @ Y)
    order = np.argsort(-ev)
    F = np.zeros((6, 6)); w = np.zeros(3)
    for b in range(3):
        idx = order[2*b:2*b+2]
        Vb = V[:, idx]
        e1 = Vb @ (Vb.T @ _REF); e1 /= np.linalg.norm(e1)
        e2 = Y @ e1; nrm = np.linalg.norm(e2); w[b] = nrm; e2 /= nrm
        F[:, 2*b] = e1; F[:, 2*b+1] = e2
    return F, w


def canon_frame(Y):
    if SMOOTH: return canon_frame_smooth(Y)
    T, Z = schur(Y, output='real')
    w = np.array([abs(T[0, 1]), abs(T[2, 3]), abs(T[4, 5])])
    return Z, w


def best_cd(G, ngrid=36, nref=6):
    """max over c,d in T^3 of c^T G d.  returns (val, c, d)."""
    th = np.linspace(0, 2 * np.pi, ngrid, endpoint=False)
    gx = np.stack(np.meshgrid(th, th, th, indexing='ij'), -1).reshape(-1, 3)
    D = np.zeros((len(gx), 6)); D[:, 0::2] = np.cos(gx); D[:, 1::2] = np.sin(gx)
    GD = D @ G.T                        # (N,6)
    nb = np.sqrt(GD[:, 0::2]**2 + GD[:, 1::2]**2).sum(1)
    idx = np.argsort(-nb)[:nref]
    best = (-1, None, None)
    def negval(t):
        d = np.zeros(6); d[0::2] = np.cos(t); d[1::2] = np.sin(t)
        g = G @ d
        return -np.sqrt(g[0::2]**2 + g[1::2]**2).sum()
    for i in idx:
        r = minimize(negval, gx[i], method='BFGS')
        if -r.fun > best[0]:
            t = r.x; d = np.zeros(6); d[0::2] = np.cos(t); d[1::2] = np.sin(t)
            g = G @ d; c = np.zeros(6)
            for b in range(3):
                nrm = np.linalg.norm(g[2*b:2*b+2]); c[2*b:2*b+2] = g[2*b:2*b+2] / max(nrm, 1e-300)
            best = (-r.fun, c, d)
    return best


def f_ss(K, Y, A0=None, Ar=None, maxcuts=400, tol=1e-7, verbose=False):
    if A0 is None:
        A0, Ar, resid, rank = affine_family(K, Y)
    wK = np.array([K[0, 1], K[2, 3], K[4, 5]])
    _, Uc = block_basis(np.eye(6), np.abs(wK))
    FY, wY = canon_frame(Y)
    _, Vc = block_basis(FY, wY)   # careful naming: Uc = K-side (right vec Xv), Vc = Y-side (left Xu)
    B0 = BS(A0); Br = np.array([BS(A) for A in Ar])
    # G(z) = Vc B(z) Uc^T  -> (6,6): <Xu_j, L_A Xv_k>
    G0 = Vc @ B0 @ Uc.T
    Gr = np.array([Vc @ B @ Uc.T for B in Br])
    r = len(Gr)
    cuts = []   # list of (c,d)
    rng = np.random.default_rng(0)
    # initial cuts
    for _ in range(30):
        c = np.zeros(6); d = np.zeros(6)
        a = rng.uniform(0, 2*np.pi, 3); b = rng.uniform(0, 2*np.pi, 3)
        c[0::2] = np.cos(a); c[1::2] = np.sin(a); d[0::2] = np.cos(b); d[1::2] = np.sin(b)
        cuts.append((c, d))
    z = np.zeros(r); lo = -np.inf
    for it in range(maxcuts):
        # LP: min t s.t. t >= c^T (G0 + sum z G_r) d
        Aub = np.array([np.concatenate([[-1.0], [c @ Gr[k] @ d for k in range(r)]]) for c, d in cuts])
        bub = np.array([-(c @ G0 @ d) for c, d in cuts])
        res = linprog(np.concatenate([[1.0], np.zeros(r)]), A_ub=Aub, b_ub=bub, bounds=[(None, None)] * (r + 1), method='highs')
        lo = res.x[0]; z = res.x[1:]
        G = G0 + np.tensordot(z, Gr, axes=(0, 0))
        val, c, d = best_cd(G)
        if verbose: print(it, "lower", lo, "upper(z)", val)
        if val - lo < tol:
            return val, lo, z
        cuts.append((c, d))
    return val, lo, z
