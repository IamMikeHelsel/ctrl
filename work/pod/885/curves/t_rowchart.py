import sys
from deform2 import solve, rationalise, Z0, pari, polys
fixed={("a",i,k):Z0[("a",i,k)] for i in (0,2) for k in range(3)}
print("a0",[str(fixed[("a",0,k)]) for k in range(3)],"a2",[str(fixed[("a",2,k)]) for k in range(3)])
for d in ["1/50","1/20","1/10"]:
    f=dict(fixed); f[("a",2,0)]=Z0[("a",2,0)]+pari(d)*Z0[("a",2,0)]
    f[("a",2,1)]=Z0[("a",2,1)]-pari(d)*3
    z,res,it=solve(f)
    q,bad=rationalise(z)
    print(d,"res",pari.precision(res,4),"its",it,"non-rational coords",bad,"of",len(z),flush=True)
    if bad==0:
        P=polys(q)
        for j in range(7): print("  C",j,pari.factor(P[("C",j)]) if P[("C",j)]!=0 else 0)
