"""Structured comparator classes C (linear subspaces of Sym_6) and
   g_C(K,Y) = min_z sigma_max( B_S(A(z)) restricted to columns in C )     (convex SDP in z)
g_C >= 1 means: for every A in the affine family some V in C has ||L_A V|| >= ||V||.
Classes:
  C9K : V commuting with K^2 (block-diagonal in K's frame), contains all same-square comparators of K
  C9Y : same for Y (used through A^T side: equivalently U side)  -- here as right vectors for A^T
  C6K : span{KT}: block-diagonal, traceless per block
  C9K+C9Y : sum of the two subspaces (dim 18)"""
import numpy as np
import cvxpy as cp
from core import *
from ssclass import frame

def block_basis(X, traceless=False):
    F, w = frame(X)
    out = []
    for i in range(3):
        mats = [np.diag([1., -1.]), np.array([[0., 1.], [1., 0.]])] + ([] if traceless else [np.eye(2)])
        for R in mats:
            M = np.zeros((6, 6)); M[2*i:2*i+2, 2*i:2*i+2] = R
            out.append(F @ M @ F.T)
    return np.array(out)

def orth_coords(mats):
    C = np.array([scoords(M) for M in mats]).T     # 21 x d
    u, s, vt = np.linalg.svd(C, full_matrices=False)
    return u[:, s > 1e-10 * s[0]]

def class_Q(K, Y, name):
    if name == 'C9K': return orth_coords(block_basis(K))
    if name == 'C6K': return orth_coords(block_basis(K, True))
    if name == 'C9Y': return orth_coords(block_basis(Y))
    if name == 'C9K+C9Y': return orth_coords(np.concatenate([block_basis(K), block_basis(Y)]))
    if name == 'full': return np.eye(21)
    raise ValueError(name)

def g_class(K, Y, name, A0=None, Ar=None, side='right'):
    """side='right': V in C (right vectors of B_S(A)); side='left': U in C (i.e. right vectors of B_S(A)^T = B_S(A^T))."""
    if A0 is None:
        A0, Ar, res = affine_family(K, Y)
    Q = class_Q(K, Y, name)
    B0 = BS(A0); Br = [BS(Ai) for Ai in Ar]
    if side == 'left':
        B0 = B0.T; Br = [B.T for B in Br]
    m, d = 21, Q.shape[1]
    z = cp.Variable(len(Br)); t = cp.Variable()
    B = (B0 + sum(z[i] * Br[i] for i in range(len(Br)))) @ Q
    con = cp.bmat([[t * np.eye(m), B], [B.T, t * np.eye(d)]]) >> 0
    prob = cp.Problem(cp.Minimize(t), [con])
    prob.solve(solver=cp.CLARABEL)
    return float(t.value), z.value
