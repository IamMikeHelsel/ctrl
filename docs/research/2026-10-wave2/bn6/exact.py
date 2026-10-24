"""Exact rational certificates for k(A)/s(A) bounds (independent of the ctrl pod code).

Lower bound on k: for a rational skew K, k(A)^2 >= ||L_A K||^2/||K||^2 (exact Fraction).
Upper bound on s: parametrise X in Sym_n by upper-triangular coordinates x; ||X||_F^2 = x^T G x,
||L_A X||_F^2 = x^T M x with G, M rational. If c*G - M is positive definite (exact LDL^T, all
pivots > 0) then s(A)^2 < c.  Analogous routine for upper bound on k and lower bound on s.
"""
from fractions import Fraction as Fr
import itertools

def mat(A): return [[Fr(x) for x in row] for row in A]
def mul(A,B):
    n=len(A); m=len(B[0]); p=len(B)
    return [[sum(A[i][l]*B[l][j] for l in range(p)) for j in range(m)] for i in range(n)]
def T(A): return [list(r) for r in zip(*A)]
def add(A,B): return [[a+b for a,b in zip(ra,rb)] for ra,rb in zip(A,B)]
def lyap(A,X): return add(mul(A,X),mul(X,T(A)))
def fro2(X): return sum(x*x for r in X for x in r)

def coords(n,kind):
    if kind=='sym': return [(i,j) for i in range(n) for j in range(i,n)]
    return [(i,j) for i in range(n) for j in range(i+1,n)]

def unit(n,i,j,kind):
    E=[[Fr(0)]*n for _ in range(n)]
    E[i][j]=Fr(1)
    if i!=j: E[j][i]=Fr(1) if kind=='sym' else Fr(-1)
    return E

def gram(A,kind):
    n=len(A); C=coords(n,kind)
    imgs=[lyap(A,unit(n,i,j,kind)) for (i,j) in C]
    m=len(C)
    M=[[sum(imgs[a][r][c]*imgs[b][r][c] for r in range(n) for c in range(n)) for b in range(m)] for a in range(m)]
    G=[[Fr(0)]*m for _ in range(m)]
    for a,(i,j) in enumerate(C): G[a][a]=Fr(1) if i==j else Fr(2)
    return G,M

def is_pd(S):
    S=[row[:] for row in S]; m=len(S); piv=[]
    for k in range(m):
        p=S[k][k]
        if p<=0: return False,piv
        piv.append(p)
        for i in range(k+1,m):
            f=S[i][k]/p
            if f:
                for j in range(k+1,m): S[i][j]-=f*S[k][j]
    return True,piv

def s2_upper(A,c,kind='sym'):
    """True iff c*G - M > 0, i.e. sup over kind of ||L_A X||^2/||X||^2 < c."""
    G,M=gram(A,kind)
    m=len(G)
    ok,piv=is_pd([[c*G[i][j]-M[i][j] for j in range(m)] for i in range(m)])
    return ok

def ratio_lower(A,K):
    return fro2(lyap(A,K))/fro2(K)
