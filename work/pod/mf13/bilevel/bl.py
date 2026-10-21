"""Core library for the bilevel search (general n, used for n=6 and n=7 positive control).

Conventions
  L_A(X) = A X + X A^T,   S_n symmetric, K_n skew.
  Conjecture (Byers-Nash / Kressner-Vandereycken):  ||L_A|K|| <= ||L_A|S||.
  Counterexample: ||L_A|K|| > ||L_A|S||.
  Skew singular pair (K,Y) with value 1:  A K + K A^T = Y ,  A^T Y + Y A = K,  ||K||_F=||Y||_F=1.
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
    """T_S[p,q,i,j] = <S_i, L_{E_pq}(S_j)>  so that B_S(A) = sum_pq A[p,q] T_S[p,q]."""
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


def BS(A):
    n = A.shape[0]
    return np.tensordot(A, optensors(n)[0], axes=([0, 1], [0, 1]))


def BK(A):
    n = A.shape[0]
    return np.tensordot(A, optensors(n)[1], axes=([0, 1], [0, 1]))


def norms(A):
    """(sym restricted norm, skew restricted norm) by direct SVD of orthonormal-basis matrices."""
    return np.linalg.norm(BS(A), 2), np.linalg.norm(BK(A), 2)


def full_op_matrix_norms(A):
    """Independent check: build the n^2 x n^2 operator (I (x) A + A (x) I), restrict to sym / skew via projectors."""
    n = A.shape[0]
    I = np.eye(n)
    M = np.kron(I, A) + np.kron(A, I)      # column-wise vec: vec(AX+XA^T)
    # permutation P: vec(X) -> vec(X^T)
    P = np.zeros((n * n, n * n))
    for i in range(n):
        for j in range(n):
            P[j * n + i, i * n + j] = 1   # vec index (col-major) of X[i,j] is j*n+i ; X^T[j,i] at i*n+j
    Ps = (np.eye(n * n) + P) / 2
    Pk = (np.eye(n * n) - P) / 2
    # orthonormal basis of ranges
    def rng(Pr):
        u, s, vt = np.linalg.svd(Pr)
        return u[:, s > 0.5]
    Us, Uk = rng(Ps), rng(Pk)
    return np.linalg.norm(Us.T @ M @ Us, 2), np.linalg.norm(Uk.T @ M @ Uk, 2)


def skew_top_pair(A):
    """Top singular triple of L_A|K: returns sigma, K, Y (unit Frobenius)."""
    n = A.shape[0]
    Sb, Kb = bases(n)
    B = BK(A)
    u, s, vt = np.linalg.svd(B)
    K = np.tensordot(vt[0], Kb, axes=(0, 0))
    Y = np.tensordot(u[:, 0], Kb, axes=(0, 0))
    return s[0], K, Y, s


# ---------------- affine family of A having (K,Y) as skew singular pair with value 1 ----------------

@lru_cache(None)
def _pairmaps(n):
    """Linear maps  A -> A K + K A^T  needs K; build lazily. Return helper index arrays."""
    return None


def pair_matrix(K, Y):
    """M (2*m x n^2) acting on vec_rowmajor(A) with  M a = [vecK-coords(AK+KA^T); vecK-coords(A^T Y + Y A)], rhs = [coords(Y); coords(K)]."""
    n = K.shape[0]
    Sb, Kb = bases(n)
    m = len(Kb)
    # d/dA[p,q] of (A K + K A^T) = E_pq K + K E_qp
    M = np.zeros((2 * m, n * n))
    # vectorized: for each (p,q): E K = outer(e_p, K[q,:]);  K E^T = outer(K[:,q], e_p)
    # coords on Kb: <Kb_i, Z> ; Z skew automatically after sum? E K + K E^T is not skew in general; sum is symmetric part? use full inner product
    # (A K + K A^T) is skew? (AK+KA^T)^T = K^T A^T + A K^T = -(KA^T + AK) -> yes skew. So inner prod with Kb is exact.
    for p in range(n):
        for q in range(n):
            Z1 = np.zeros((n, n)); Z1[p, :] += K[q, :]; Z1[:, p] += K[:, q]   # E_pq K + K E_qp  -> wait: K E_pq^T=K E_qp : column p gets K[:,q]
            # second equation: A^T Y + Y A : d/dA[p,q] = E_qp Y + Y E_pq : row q gets Y[p,:]; column q gets Y[:,p]
            Z2 = np.zeros((n, n)); Z2[q, :] += Y[p, :]; Z2[:, q] += Y[:, p]
            M[:m, p * n + q] = np.einsum('iab,ab->i', Kb, Z1)
            M[m:, p * n + q] = np.einsum('iab,ab->i', Kb, Z2)
    rhs = np.concatenate([np.einsum('iab,ab->i', Kb, Y), np.einsum('iab,ab->i', Kb, K)])
    return M, rhs


@lru_cache(None)
def _pm_tensors(n):
    """Precompute tensors so pair_matrix is a fast einsum:  M1[i,p,q] etc."""
    Sb, Kb = bases(n)
    # Z1[p,q] = E_pq K + K E_qp: Z1[a,b] = delta_ap K[q,b] + K[a,q] delta_bp
    # coords_i = sum_ab Kb[i,a,b] Z1[a,b] = sum_b Kb[i,p,b] K[q,b] + sum_a Kb[i,a,p] K[a,q]
    # Z2[a,b] = delta_aq Y[p,b] + Y[a,p] delta_bq -> coords = sum_b Kb[i,q,b]Y[p,b] + sum_a Kb[i,a,q] Y[a,p]
    return Kb


def pair_matrix_fast(K, Y):
    n = K.shape[0]
    Kb = _pm_tensors(n)
    m = len(Kb)
    # M1[i,p,q] = sum_b Kb[i,p,b] K[q,b] + sum_a Kb[i,a,p] K[a,q]
    M1 = np.einsum('ipb,qb->ipq', Kb, K) + np.einsum('iap,aq->ipq', Kb, K)
    # M2[i,p,q] = sum_b Kb[i,q,b] Y[p,b] + sum_a Kb[i,a,q] Y[a,p]
    M2 = np.einsum('iqb,pb->ipq', Kb, Y) + np.einsum('iaq,ap->ipq', Kb, Y)
    M = np.concatenate([M1.reshape(m, n * n), M2.reshape(m, n * n)], axis=0)
    rhs = np.concatenate([np.einsum('iab,ab->i', Kb, Y), np.einsum('iab,ab->i', Kb, K)])
    return M, rhs


def affine_family(K, Y, rtol=1e-9, return_info=False):
    """All A with (K,Y) skew singular pair of value 1:  A = A0 + sum z_r A_r.
    Returns (A0, [A_r], resid, rank)."""
    n = K.shape[0]
    M, rhs = pair_matrix_fast(K, Y)
    u, s, vt = np.linalg.svd(M, full_matrices=True)
    tol = rtol * s[0]
    rank = int((s > tol).sum())
    # min-norm LS solution
    a0 = vt[:rank].T @ ((u[:, :rank].T @ rhs) / s[:rank])
    resid = np.linalg.norm(M @ a0 - rhs)
    null = vt[rank:]
    A0 = a0.reshape(n, n)
    Ar = null.reshape(-1, n, n)
    if return_info:
        return A0, Ar, resid, rank, s
    return A0, Ar, resid, rank


def inner_min(A0, Ar, solver='clarabel', warm=None, return_z=False):
    """min_z ||B_S(A0 + sum z_r A_r)||_2   via SDP (cvxpy)."""
    import cvxpy as cp
    n = A0.shape[0]
    B0 = BS(A0)
    Br = np.array([BS(A) for A in Ar])
    m = B0.shape[0]
    r = len(Br)
    z = cp.Variable(r)
    t = cp.Variable()
    B = B0 + sum(z[i] * Br[i] for i in range(r)) if r > 0 else B0
    cons = [cp.bmat([[t * np.eye(m), B], [B.T, t * np.eye(m)]]) >> 0]
    prob = cp.Problem(cp.Minimize(t), cons)
    prob.solve(solver=cp.CLARABEL)
    zz = z.value if r > 0 else np.zeros(0)
    if return_z:
        return float(t.value), zz
    return float(t.value)
