"""Fast inner solver: min_z sigma_max(B0 + sum z_r B_r) via Clarabel directly (no cvxpy overhead)."""
import numpy as np
import scipy.sparse as sp
import clarabel
from functools import lru_cache
from bl import BS


@lru_cache(None)
def _tri_index(m2):
    """index map for upper-triangle col-stacked svec of an m2 x m2 matrix"""
    idx = {}
    k = 0
    for j in range(m2):
        for i in range(j + 1):
            idx[(i, j)] = k
            k += 1
    return idx, k


@lru_cache(None)
def _brow(m):
    idx, _ = _tri_index(2 * m)
    ii, jj = np.meshgrid(np.arange(m), np.arange(m), indexing='ij')
    return np.array([idx[(i, m + j)] for i, j in zip(ii.ravel(), jj.ravel())])


@lru_cache(None)
def _drows(m):
    idx, _ = _tri_index(2 * m)
    return np.array([idx[(i, i)] for i in range(2 * m)])


def sdp_sigma_min(B0, Br, tol=1e-10, return_all=False, max_iter=200):
    """min_{t,z} t  s.t. [[tI,B],[B^T,tI]] >= 0, B = B0 + sum z_r Br[r]. Returns (t, z)."""
    m = B0.shape[0]
    r = len(Br)
    m2 = 2 * m
    idx, nsv = _tri_index(m2)
    sq2 = np.sqrt(2.0)
    # s = b - A x must lie in PSD cone, with x=(t,z).  M(x) = [[tI,B],[B^T,tI]] =: Mc  ->  need Mc PSD
    # clarabel: A x + s = b, s in cone.  so  s = b - A x ;  want s = svec(M(x)) = svec(M0) + t*svec(Mt) + sum z svec(Mr)
    # => b = svec(M0), A = -[svec(Mt), svec(Mr)...]
    def svec_blockB(Bm):
        """svec of [[0,Bm],[Bm^T,0]] -> returns (rows, vals). Only the upper-right block entries (i<m<=j) are nonzero."""
        ii, jj = np.meshgrid(np.arange(m), np.arange(m), indexing='ij')
        rows = np.array([idx[(i, m + j)] for i, j in zip(ii.ravel(), jj.ravel())])
        return rows, Bm.ravel() * sq2
    rows_all = []; cols_all = []; vals_all = []
    # t column: diag entries =1 (unscaled for diagonal)
    drows = _drows(m)
    rows_all.append(drows); cols_all.append(np.zeros(m2, int)); vals_all.append(-np.ones(m2))
    # z columns
    brow = _brow(m)
    for k in range(r):
        rows_all.append(brow); cols_all.append(np.full(m * m, k + 1)); vals_all.append(-Br[k].ravel() * sq2)
    A = sp.csc_matrix((np.concatenate(vals_all), (np.concatenate(rows_all), np.concatenate(cols_all))), shape=(nsv, r + 1))
    b = np.zeros(nsv)
    b[brow] = B0.ravel() * sq2
    P = sp.csc_matrix((r + 1, r + 1))
    q = np.zeros(r + 1); q[0] = 1.0
    settings = clarabel.DefaultSettings()
    settings.verbose = False
    settings.tol_gap_abs = tol; settings.tol_gap_rel = tol; settings.tol_feas = tol
    settings.max_iter = max_iter
    solver = clarabel.DefaultSolver(P, q, A, b, [clarabel.PSDTriangleConeT(m2)], settings)
    sol = solver.solve()
    x = np.array(sol.x)
    if return_all:
        return x[0], x[1:], sol
    return x[0], x[1:]


def inner_f(A0, Ar, tol=1e-10):
    B0 = BS(A0)
    Br = [BS(A) for A in Ar]
    t, z = sdp_sigma_min(B0, Br, tol=tol)
    # polish: true sigma_max at returned z
    B = B0 + sum(zi * Bi for zi, Bi in zip(z, Br))
    smax = np.linalg.norm(B, 2)
    return smax, z
