"""Core tools for the n=6 proof attempt (self-contained; generic n where possible).

Conventions
  L_A(X) = A X + X A^T ; S_n symmetric, K_n skew ; Frobenius inner product.
  Skew singular pair with value 1:  A K + K A^T = Y,  A^T Y + Y A = K,  |K|_F = |Y|_F = 1.
  f(K,Y) = min over the affine family of such A of s(A) = ||L_A|S_n||.
  Dual:  f = max { sum_k sig_k <U_k, L_A V_k> : sum_k sig_k |U_k||V_k| <= 1, z-independent }.
"""
import numpy as np
from functools import lru_cache

J2 = np.array([[0., 1.], [-1., 0.]])


@lru_cache(None)
def bases(n):
    Sb, Kb = [], []
    for i in range(n):
        M = np.zeros((n, n)); M[i, i] = 1; Sb.append(M)
    for i in range(n):
        for j in range(i + 1, n):
            M = np.zeros((n, n)); M[i, j] = M[j, i] = 1 / np.sqrt(2); Sb.append(M)
    for i in range(n):
        for j in range(i + 1, n):
            M = np.zeros((n, n)); M[i, j] = 1 / np.sqrt(2); M[j, i] = -1 / np.sqrt(2); Kb.append(M)
    return np.array(Sb), np.array(Kb)


@lru_cache(None)
def optensors(n):
    Sb, Kb = bases(n)
    out = []
    for B in (Sb, Kb):
        m = len(B)
        T = np.zeros((n, n, m, m))
        for p in range(n):
            for q in range(n):
                E = np.zeros((n, n)); E[p, q] = 1
                LX = np.einsum('ab,jbc->jac', E, B) + np.einsum('jab,cb->jac', B, E)
                T[p, q] = np.einsum('iac,jac->ij', B, LX)
        out.append(T)
    return out[0], out[1]


def L(A, X):
    return A @ X + X @ A.T


def BS(A):
    return np.tensordot(A, optensors(A.shape[0])[0], axes=([0, 1], [0, 1]))


def BK(A):
    return np.tensordot(A, optensors(A.shape[0])[1], axes=([0, 1], [0, 1]))


def norms(A):
    return np.linalg.norm(BS(A), 2), np.linalg.norm(BK(A), 2)


def sym_of(v, n=6):
    return np.tensordot(v, bases(n)[0], axes=(0, 0))


def skew_of(v, n=6):
    return np.tensordot(v, bases(n)[1], axes=(0, 0))


def scoords(X):
    return np.einsum('iab,ab->i', bases(X.shape[0])[0], X)


def kcoords(X):
    return np.einsum('iab,ab->i', bases(X.shape[0])[1], X)


def make_K(*w):
    n = 2 * len(w)
    K = np.zeros((n, n))
    for i, a in enumerate(w):
        K[2 * i:2 * i + 2, 2 * i:2 * i + 2] = a * J2
    return K


# ---------------- compatibility ----------------
def moments(K, Y):
    YK = Y @ K
    D = Y @ Y - K @ K
    out = []
    P = D.copy()
    for j in range(3):
        out.append(np.trace(P))
        P = YK @ P
    return np.array(out)


def project_Y(K, Y0, iters=60, tol=1e-15):
    """Gauss-Newton on the 3 moments, Y in K_6 coordinates (FD-free analytic Jacobian)."""
    n = K.shape[0]
    Kb = bases(n)[1]
    y = kcoords(Y0)
    for it in range(iters):
        Y = skew_of(y, n)
        m = moments(K, Y)
        if np.linalg.norm(m) < tol:
            return Y, np.linalg.norm(m)
        YK = Y @ K; D = Y @ Y - K @ K; YK2 = YK @ YK
        Jm = np.zeros((3, len(Kb)))
        for i, E in enumerate(Kb):
            EK = E @ K; dD = E @ Y + Y @ E
            Jm[:, i] = (np.trace(dD), np.trace(EK @ D) + np.trace(YK @ dD),
                        np.trace((EK @ YK + YK @ EK) @ D) + np.trace(YK2 @ dD))
        dy = np.linalg.lstsq(Jm, -m, rcond=1e-12)[0]
        nd = np.linalg.norm(dy)
        if nd > 0.5: dy *= 0.5 / nd
        y = y + dy
    Y = skew_of(y, n)
    return Y, np.linalg.norm(moments(K, Y))


def random_pair(rng, w=None, Y0=None):
    if w is None:
        w = rng.uniform(0.05, 1, 3)
    w = np.asarray(w, float); w = w / np.linalg.norm(w) / np.sqrt(2)
    K = make_K(*w)
    if Y0 is None:
        Y0 = skew_of(rng.standard_normal(15)); Y0 /= np.linalg.norm(Y0)
    Y, err = project_Y(K, Y0)
    return K, Y, err


# ---------------- affine family ----------------
def pair_matrix(K, Y):
    n = K.shape[0]
    Kb = bases(n)[1]
    m = len(Kb)
    M1 = np.einsum('ipb,qb->ipq', Kb, K) + np.einsum('iap,aq->ipq', Kb, K)
    M2 = np.einsum('iqb,pb->ipq', Kb, Y) + np.einsum('iaq,ap->ipq', Kb, Y)
    M = np.concatenate([M1.reshape(m, n * n), M2.reshape(m, n * n)], axis=0)
    rhs = np.concatenate([kcoords(Y), kcoords(K)])
    return M, rhs


def affine_family(K, Y, rtol=1e-9):
    n = K.shape[0]
    M, rhs = pair_matrix(K, Y)
    u, s, vt = np.linalg.svd(M, full_matrices=True)
    rank = int((s > rtol * s[0]).sum())
    a0 = vt[:rank].T @ ((u[:, :rank].T @ rhs) / s[:rank])
    resid = np.linalg.norm(M @ a0 - rhs)
    return a0.reshape(n, n), vt[rank:].reshape(-1, n, n), resid


# ---------------- inner problem ----------------
def inner_cvx(K, Y, A0=None, Ar=None):
    """Solve f = min_z sigma_max(B_S(A(z))) with Clarabel; return f, A*, dual W (m x m, nuclear norm 1)."""
    import cvxpy as cp
    if A0 is None:
        A0, Ar, resid = affine_family(K, Y)
    B0 = BS(A0); Br = np.array([BS(A) for A in Ar]); m = B0.shape[0]; r = len(Br)
    z = cp.Variable(r); t = cp.Variable()
    B = B0 + sum(z[i] * Br[i] for i in range(r))
    Z = cp.bmat([[t * np.eye(m), B], [B.T, t * np.eye(m)]])
    con = Z >> 0
    prob = cp.Problem(cp.Minimize(t), [con])
    prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12)
    Lam = con.dual_value
    W = -2 * Lam[:m, m:]          # <W,B> = f with ||W||_* = 1 (sign: maximise <W,B>)
    zz = z.value
    A = A0 + np.tensordot(zz, Ar, axes=(0, 0))
    return float(t.value), A, W, dict(A0=A0, Ar=Ar, B0=B0, Br=Br, z=zz)


def inner_barrier(K, Y, tol=1e-11):
    import sys
    sys.path.insert(0, '/Users/mike/dev/ctrl/work/pod/mf13/bilevel')
    from barrier import barrier_min_sigma
    A0, Ar, resid = affine_family(K, Y)
    B0 = BS(A0); Br = np.array([BS(A) for A in Ar])
    fval, z, t, nit = barrier_min_sigma(B0, Br, tol=tol)
    A = A0 + np.tensordot(z, Ar, axes=(0, 0))
    return fval, A, dict(A0=A0, Ar=Ar, B0=B0, Br=Br, z=z, resid=resid)


def dual_terms(W, n=6, cut=1e-6):
    """SVD of dual W -> list of (sigma, U (left, Y-side), V (right, K-side)) symmetric unit matrices."""
    u, s, vt = np.linalg.svd(W)
    out = []
    for k in range(len(s)):
        if s[k] < cut * s[0]: break
        out.append((s[k], sym_of(u[:, k], n), sym_of(vt[k], n)))
    return out
