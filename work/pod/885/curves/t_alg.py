import sys
from deform_newton import solve, pari, polys, inc
r=pari(sys.argv[1]); s=pari(sys.argv[2])
z,res=solve(r,s,verbose=False)
print("res",pari.precision(res,5))
P=polys(z,r,s)
for key in [("C",2),("C",0),("C",4),("a",0),("a",1)]:
    for k in range(3):
        v=pari.polcoef(P[key],k)
        print(key,k, pari.algdep(v,4), pari.algdep(v,8))
