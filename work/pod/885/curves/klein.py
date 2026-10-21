"""Klein four-group V of root pairings: does every column of a configuration have its roots as a V-orbit?"""
from fractions import Fraction as F
import json, sys
import cypari2
pari=cypari2.Pari()
INF=None
def mob(M,z):
    a,b,c,d=M
    if z is INF: return INF if c==0 else F(a)/c
    den=c*z+d
    if den==0: return INF
    return (a*z+b)/den
def invol(p,q,r,s):
    """Moebius involution swapping p<->q and r<->s: z -> (a z + b)/(c z - a)."""
    # involution: c z w - a(z+w) - b = 0 for pairs (z,w)
    import itertools
    def row(z,w):
        if z is INF: return (w, -1, 0) if False else None
        return (z*w, -(z+w), -1)   # coefficients of (c, a, b)
    r1=row(p,q); r2=row(r,s)
    # solve r1.(c,a,b)=0, r2.(c,a,b)=0 -> cross product
    c=r1[1]*r2[2]-r1[2]*r2[1]; a=r1[2]*r2[0]-r1[0]*r2[2]; b=r1[0]*r2[1]-r1[1]*r2[0]
    return (a,b,c,-a)
def roots(poly):
    p=pari(poly); out=[]
    for f in pari.factor(p)[0]:
        if pari.poldegree(f)==1: out.append(F(str(-pari.polcoef(f,0)/pari.polcoef(f,1))))
        elif pari.poldegree(f)>1: out.append(('irr',str(f)))
    if pari.poldegree(p)<4 and p!=0: out.append(INF)
    return out
if __name__=="__main__":
    d=json.load(open(sys.argv[1]))
    C=[c for c in d["C"] if c!="0"]; base=int(sys.argv[2]) if len(sys.argv)>2 else 0; C=[C[base]]+[c for i,c in enumerate(C) if i!=base]
    r1=roots(C[0]); print("C0 roots",r1)
    Vs=[invol(r1[0],r1[1],r1[2],r1[3]),invol(r1[0],r1[2],r1[1],r1[3]),invol(r1[0],r1[3],r1[1],r1[2])]
    for j,c in enumerate(C):
        rs=roots(c)
        if any(isinstance(x,tuple) for x in rs): print(j,"irreducible factors",rs); continue
        ok=all(set(mob(M,z) for z in rs)==set(rs) for M in Vs)
        print(j,rs,"V-orbit:",ok)
