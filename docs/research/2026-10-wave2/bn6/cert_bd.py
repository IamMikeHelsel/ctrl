"""Exact obstruction certificate: for rational A (6x6) and rational skew Kt (rounded top skew singular
vector of L_A), prove  sup_{S in Sym ∩ comm(Kt^2)} ||L_A S||^2/||S||^2  <  c  <  ||L_A Kt||^2/||Kt||^2
with exact rational arithmetic (sympy nullspace + Fraction LDL^T).
Usage: python3 cert_bd.py points.json idx denom"""
import sys, json, numpy as np, sympy as sp
from fractions import Fraction as Fr
from exact import is_pd
from core import bases, op_mats, top_pair

def rat(x,den): return Fr(int(round(x*den)),den)

def certify(A_f, den=10**6, margin=Fr(1,1000)):
    n=6
    A_f=A_f/np.abs(A_f).max()
    A=sp.Matrix([[sp.Rational(rat(x,den).numerator,rat(x,den).denominator) for x in r] for r in A_f])
    Af=np.array(A.tolist(),dtype=float)
    S,Kb=bases(n); LS,LK=op_mats(Af); k,Y,K,sv=top_pair(LK,Kb)
    K=K/np.abs(K).max()
    Kt=sp.zeros(n,n)
    for i in range(n):
        for j in range(i+1,n):
            q=rat(K[i,j],den); Kt[i,j]=sp.Rational(q.numerator,q.denominator); Kt[j,i]=-Kt[i,j]
    L=lambda X: A*X+X*A.T
    fro2=lambda X: sum(x**2 for x in X)
    E=fro2(L(Kt))/fro2(Kt)
    # basis of Sym, nullspace of S -> S Kt^2 - Kt^2 S
    K2=Kt*Kt
    symb=[]
    for i in range(n):
        for j in range(i,n):
            M=sp.zeros(n,n); M[i,j]=1; M[j,i]=1; symb.append(M)
    Mat=sp.Matrix([[ (B*K2-K2*B)[r,c] for B in symb] for r in range(n) for c in range(n)])
    ns=Mat.nullspace()
    BD=[sum((v[t]*symb[t] for t in range(len(symb))),sp.zeros(n,n)) for v in ns]
    m=len(BD)
    imgs=[L(B) for B in BD]
    ip=lambda X,Y: sum(X[t]*Y[t] for t in range(n*n))
    G=[[Fr(str(ip(BD[a],BD[b]))) for b in range(m)] for a in range(m)]
    Mm=[[Fr(str(ip(imgs[a],imgs[b]))) for b in range(m)] for a in range(m)]
    Ef=Fr(str(E))
    c=Ef*(1-margin)
    # find smallest certified c by bisection on margin grid
    best=None
    for mg in [Fr(1,10**6),Fr(2,10**6),Fr(3,10**6),Fr(1,1000),Fr(5,1000),Fr(1,100),Fr(2,100),Fr(3,100),Fr(5,100)]:
        cc=Ef*(1-mg)
        ok,_=is_pd([[cc*G[i][j]-Mm[i][j] for j in range(m)] for i in range(m)])
        if ok: best=mg
    # float sanity
    cos=abs(np.sum(np.array(Kt.tolist(),float)*K))/np.linalg.norm(np.array(Kt.tolist(),float))/np.linalg.norm(K)
    return dict(dimBD=m, E=float(Ef), certified_margin=str(best) if best is not None else None,
                k2_over_k1=sv[1]/sv[0], cos_Kt_topK=cos, A=[[str(x) for x in r] for r in A.tolist()],
                Kt=[[str(x) for x in r] for r in Kt.tolist()],
                moduli=sorted(np.abs(np.linalg.eigvals(np.array(Kt.tolist(),float))).round(4).tolist())[::2])

if __name__=='__main__':
    pts=json.load(open(sys.argv[1])); i=int(sys.argv[2]); den=int(sys.argv[3]) if len(sys.argv)>3 else 10**6
    res=certify(np.array(pts[i]['A']),den)
    print({k:v for k,v in res.items() if k not in ('A','Kt')})
    json.dump(res,open(f'cert_bd_{sys.argv[1].split(".")[0]}_{i}.json','w'),indent=1)
