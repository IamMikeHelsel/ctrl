from deform2 import solve, Z0, pari, polys
from algdeg import report
fixed={("a",i,k):Z0[("a",i,k)] for i in (0,2) for k in range(3)}
f=dict(fixed); f[("a",2,0)]=Z0[("a",2,0)]+pari("1/20")*Z0[("a",2,0)]; f[("a",2,1)]=Z0[("a",2,1)]-pari("3/20")
z,res,it=solve(f)
for k,(d,p) in report(polys(z)).items(): print(k,d, pari.factor(pari.poldisc(p)) if d==2 else "")
