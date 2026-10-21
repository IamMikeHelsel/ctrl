import sys
import deform_newton as dn
from deform_newton import solve, pari, polys
pari.set_real_precision(600)
r=pari(sys.argv[1]); s=pari(sys.argv[2])
z,res=solve(r,s,its=60,verbose=False)
print("res",pari.precision(res,5))
P=polys(z,r,s)
for i in [0,2,3,4,5,6,1]:
    a2=P[("a",i)]**2
    v=pari.polcoef(a2,4)/pari.polcoef(a2,0)   # scale-free
    for deg in (1,2,3,4,6,8,12,16,24):
        p=pari.algdep(v,deg)
        if abs(pari.subst(p,'x',v))<pari("1e-400") and max(abs(c) for c in pari.Vec(p))<pari("1e60"):
            print("row",i,"deg",pari.poldegree(p),pari.factor(p)[0]); break
    else: print("row",i,"deg >24")
for j in [0,4,5,6]:
    c=P[("C",j)]; v=pari.polcoef(c,4)/pari.polcoef(c,0)
    for deg in (1,2,3,4,6,8,12,16,24):
        p=pari.algdep(v,deg)
        if abs(pari.subst(p,'x',v))<pari("1e-400") and max(abs(c) for c in pari.Vec(p))<pari("1e60"):
            print("col",j,"deg",pari.poldegree(p)); break
    else: print("col",j,"deg >24")
