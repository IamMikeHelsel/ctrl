"""Static (A-free) reformulation.
   N(P) := min { ||W||_* : sum_ij W_ij S_i S_j = P }  (S_i orthonormal basis of Sym_n)
         = min { sum |c_k| : P = sum c_k U_k V_k, U_k,V_k unit symmetric }  = dual norm of A -> s(A)/2 ... (see NOTES)
   Conjecture_n  <=>  N(Y K) <= ||Y|| ||K||  for all skew K, Y.
Also returns the optimal W (decomposition) and the primal A maximising <Y, L_A K> / s(A) (dual variable)."""
import numpy as np
import cvxpy as cp
from core import *

def N_of(P, return_W=False):
    n = P.shape[0]
    Sb = bases(n)[0]; m = len(Sb)
    # linear map W -> sum W_ij S_i S_j  as (n*n, m*m) matrix
    Mop = np.einsum('iab,jbc->acij', Sb, Sb).reshape(n * n, m * m)
    W = cp.Variable((m, m))
    X1 = cp.Variable((m, m), symmetric=True); X2 = cp.Variable((m, m), symmetric=True)
    con = [cp.bmat([[X1, W], [W.T, X2]]) >> 0, Mop @ cp.vec(W, order='C') == P.ravel()]
    prob = cp.Problem(cp.Minimize((cp.trace(X1) + cp.trace(X2)) / 2), con)
    prob.solve(solver=cp.CLARABEL)
    if return_W:
        lam = con[1].dual_value.reshape(n, n)    # dual: G with <G,P> = N, N-dual-norm(G) <= 1
        return prob.value, W.value, lam
    return prob.value

def decomposition(W, n, cut=1e-7):
    Sb = bases(n)[0]
    u, s, vt = np.linalg.svd(W)
    return [(s[k], np.tensordot(u[:, k], Sb, axes=(0, 0)), np.tensordot(vt[k], Sb, axes=(0, 0)))
            for k in range(len(s)) if s[k] > cut * s[0]]
