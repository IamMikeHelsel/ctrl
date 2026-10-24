"""Static gauge N(P) and monotone SDP ascent (independent re-implementation of the pod's Theorem 1/5 idea).

For symmetric U,V and skew Y,K:  <U, L_A V> = 2<A, UV>,  <Y, L_A K> = -2<A, YK>.
s(A) = 2 ||B(A)||_2 with B_ij = <A, S_i S_j> (S_i orthonormal basis of Sym_n).
k(A) = 2 max_{unit K,Y} <A, -Y K>.
N(P) := max { <A, P> : ||B(A)||_2 <= 1 }  (SDP). sup_A k/s = max_{unit K,Y} N(-YK).
Ascent: A -> top skew pair (K right, Y left) of L_A -> P=-YK -> A' = argmax of N(P).
Then k/s(A) <= N(P) <= k/s(A').
"""
import numpy as np, cvxpy as cp
from core import bases, op_mats, s_k, top_pair

_SS = {}
def SS(n):
    if n not in _SS:
        S, _ = bases(n)
        _SS[n] = np.einsum('iab,jbc->ijac', S, S)  # S_i S_j
    return _SS[n]

class Gauge:
    def __init__(self, n):
        self.n = n
        m = n*(n+1)//2
        P = SS(n).reshape(m*m, n*n)  # row (i,j) -> vec(S_i S_j)
        self.Ap = cp.Variable(n*n)
        self.Pp = cp.Parameter(n*n)
        Bexpr = cp.reshape(P @ self.Ap, (m, m), order='C')
        self.prob = cp.Problem(cp.Maximize(self.Pp @ self.Ap), [cp.sigma_max(Bexpr) <= 1])
    def solve(self, Pm):
        self.Pp.value = Pm.ravel()
        try:
            self.prob.solve(solver=cp.CLARABEL)
        except Exception:
            self.prob.solve(solver=cp.SCS, eps=1e-9)
        return self.prob.value, self.Ap.value.reshape(self.n, self.n)

def top_skew_P(A):
    n = A.shape[0]
    S, Kb = bases(n)
    LS, LK = op_mats(A)
    k, Y, K, _ = top_pair(LK, Kb)
    return -Y @ K, K, Y

def ascent(A, iters=60, G=None, tol=1e-10, verbose=False):
    n = A.shape[0]
    G = G or Gauge(n)
    hist = []
    for t in range(iters):
        s, k = s_k(A)
        P, K, Y = top_skew_P(A)
        Nv, A2 = G.solve(P)
        hist.append((k/s, Nv))
        if verbose: print(t, k/s, Nv)
        A = A2/np.linalg.norm(A2)
        if t > 3 and abs(hist[-1][0]-hist[-2][0]) < tol:
            break
    s, k = s_k(A)
    hist.append((k/s, None))
    return A, k/s, hist
