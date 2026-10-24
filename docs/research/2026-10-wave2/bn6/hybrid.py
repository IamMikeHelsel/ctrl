"""Hybrid comparator family: block-diagonal span (Darboux frame of top skew K) united with rank-one
symmetric comparators S = v v^T, ||L_A(vv^T)||^2 = 2(||Av||^2 + (v^T A v)^2) for unit v."""
import numpy as np
from scipy.optimize import minimize
from gap import frame, s_restricted, bd_basis

def sR1sq(A, starts=8, rng=None):
    rng = rng or np.random.default_rng(0)
    f = lambda v: -2*(np.sum((A@v)**2)/np.dot(v,v) + (v@A@v/np.dot(v,v))**2)
    U,s,Vt = np.linalg.svd(A)
    best = 0
    cands = [Vt[0], U[:,0]] + [rng.standard_normal(A.shape[0]) for _ in range(starts)]
    for v0 in cands:
        r = minimize(f, v0, method='BFGS')
        best = max(best, -r.fun)
    return best

def chyb(A):
    A1,K1,fr,k,sv = frame(A)
    sbd = s_restricted(A1, bd_basis())**2
    r1 = sR1sq(A1)
    return max(sbd, r1)/k**2, sbd/k**2, r1/k**2, fr, sv[1]/sv[0]

def sR1sq_fast(A, m=12, iters=80, seed=0):
    """Batched shifted fixed-point ascent for max_v 2(||Av||^2+(v^T A v)^2), unit v."""
    rng=np.random.default_rng(seed)
    U,s,Vt=np.linalg.svd(A)
    V=np.concatenate([Vt[:2].T,U[:,:2],rng.standard_normal((A.shape[0],m))],1)
    V/=np.linalg.norm(V,axis=0)
    AtA=A.T@A; As=A+A.T; c=2*s[0]**2+1e-9
    for _ in range(iters):
        q=np.einsum('ik,ij,jk->k',V,A,V)
        G=AtA@V+q*(As@V)+c*V
        V=G/np.linalg.norm(G,axis=0)
    vals=np.sum((A@V)**2,0)+np.einsum('ik,ij,jk->k',V,A,V)**2
    return 2*vals.max()

def chyb_fast(A):
    A1,K1,fr,k,sv = frame(A)
    sbd = s_restricted(A1, bd_basis())**2
    r1 = sR1sq_fast(A1)
    return max(sbd, r1)/k**2, sbd/k**2, r1/k**2, fr, sv[1]/sv[0]
