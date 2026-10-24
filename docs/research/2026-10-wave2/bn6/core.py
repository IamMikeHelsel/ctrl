"""Core numerics for the Byers-Nash symmetric-maximizer problem.

Convention (matches ctrl Lean `Research.ByersNashDuality.lyap`):
    L_A(X) = A X + X A^T.
(The user-facing form A^T X + X A is L_{A^T}; s and k are invariant under A -> A^T
because L_{A^T} = L_A^* and Sym/Skew are invariant subspaces.)

    s(A) = || L_A restricted to Sym_n ||   (operator norm, Frobenius on both sides)
    k(A) = || L_A restricted to Skew_n ||
    BN(n):  k(A) <= s(A) for all A in R^{n x n}.

Also provided: smin(A), kmin(A) = smallest singular values on Sym/Skew (the "sep" variant).
"""
import numpy as np


def sym_basis(n):
    B = []
    for i in range(n):
        E = np.zeros((n, n)); E[i, i] = 1.0; B.append(E)
    for i in range(n):
        for j in range(i + 1, n):
            E = np.zeros((n, n)); E[i, j] = E[j, i] = 1 / np.sqrt(2); B.append(E)
    return np.array(B)


def skew_basis(n):
    B = []
    for i in range(n):
        for j in range(i + 1, n):
            E = np.zeros((n, n)); E[i, j] = 1 / np.sqrt(2); E[j, i] = -1 / np.sqrt(2); B.append(E)
    return np.array(B)


_cache = {}


def bases(n):
    if n not in _cache:
        _cache[n] = (sym_basis(n), skew_basis(n))
    return _cache[n]


def lyap(A, X):
    return A @ X + X @ A.T


def op_mats(A):
    """Matrices of L_A on Sym_n and Skew_n in orthonormal bases (dims n(n+1)/2, n(n-1)/2)."""
    n = A.shape[0]
    S, K = bases(n)
    # L_A(B_j) coefficients: <B_i, L_A B_j>
    LS = np.einsum('iab,jab->ij', S, np.einsum('ab,jbc->jac', A, S) + np.einsum('jab,cb->jac', S, A))
    LK = np.einsum('iab,jab->ij', K, np.einsum('ab,jbc->jac', A, K) + np.einsum('jab,cb->jac', K, A))
    return LS, LK


def full_op(A):
    n = A.shape[0]
    I = np.eye(n)
    # vec column-major: vec(AX) = (I kron A) vec X ; vec(X A^T) = (A kron I) vec X
    return np.kron(I, A) + np.kron(A, I)


def s_k(A):
    LS, LK = op_mats(A)
    return np.linalg.norm(LS, 2), np.linalg.norm(LK, 2)


def s_k_min(A):
    LS, LK = op_mats(A)
    return np.linalg.svd(LS, compute_uv=False)[-1], np.linalg.svd(LK, compute_uv=False)[-1]


def top_pair(L, B):
    """Top singular triple of L, returned as matrices (left U, right V) in basis B."""
    U, s, Vt = np.linalg.svd(L)
    return s[0], np.tensordot(U[:, 0], B, 1), np.tensordot(Vt[0], B, 1), s


def ratio_and_grad(A):
    """r = k^2/s^2 and its gradient w.r.t. A (valid where top singular values are simple)."""
    n = A.shape[0]
    S, Kb = bases(n)
    LS, LK = op_mats(A)
    s, Us, Vs, _ = top_pair(LS, S)
    k, Uk, Vk, _ = top_pair(LK, Kb)
    # sigma = <U, L_A V>; d sigma/dA = U V^T + U^T V
    gs = Us @ Vs.T + Us.T @ Vs
    gk = Uk @ Vk.T + Uk.T @ Vk
    r = (k / s) ** 2
    g = r * (2 * gk / k - 2 * gs / s)
    return r, g


def darboux(K):
    """Orthogonal Q with Q K Q^T = diag(a1 J, a2 J, ...) (a's >= 0, sorted desc), J=[[0,1],[-1,0]]."""
    from scipy.linalg import schur
    n = K.shape[0]
    T, Z = schur(K, output='real')  # K = Z T Z^T
    # T is block diagonal with 2x2 blocks [[0,b],[-b,0]] (possibly with b<0) and 1x1 zeros
    Q = Z.T.copy()
    i = 0
    blocks = []
    while i < n:
        if i + 1 < n and abs(T[i + 1, i]) > 1e-14:
            b = T[i, i + 1]
            if b < 0:  # swap rows to flip sign
                Q[[i, i + 1]] = Q[[i + 1, i]]
                b = -b
            blocks.append((b, i)); i += 2
        else:
            blocks.append((0.0, i)); i += 1
    # reorder: 2x2 blocks by size desc, then zeros
    order = sorted([b for b in blocks if b[1] is not None], key=lambda t: -t[0])
    rows = []
    vals = []
    for b, i0 in order:
        if i0 + 1 < n and abs(T[i0 + 1, i0]) > 1e-14:
            rows += [i0, i0 + 1]; vals.append(b)
        else:
            rows += [i0]
    Q = Q[rows]
    return Q, np.array(vals)


def rand_A(n, rng, kind='gauss'):
    if kind == 'gauss':
        return rng.standard_normal((n, n))
    if kind == 'sparse':
        A = rng.standard_normal((n, n)) * (rng.random((n, n)) < 0.35)
        return A + 1e-3 * rng.standard_normal((n, n))
    if kind == 'nilp':
        return np.triu(rng.standard_normal((n, n)), 1) + 0.1 * rng.standard_normal((n, n))
    if kind == 'cauchy':
        return rng.standard_cauchy((n, n))
    if kind == 'lowrank':
        r = rng.integers(1, 3)
        return rng.standard_normal((n, r)) @ rng.standard_normal((r, n)) + 0.05 * rng.standard_normal((n, n))
    raise ValueError(kind)
