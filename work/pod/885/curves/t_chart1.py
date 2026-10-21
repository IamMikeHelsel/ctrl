import sys
from deform2 import solve, Z0, pari, polys, rationalise
r=pari(sys.argv[1]); s=pari(sys.argv[2])
X=pari("x")
lc=pari("220")
C1=lc*(X-4)*(X+1)*(X+4)*(X-r)
fixed={("C",1,k):pari.polcoef(C1,k) for k in range(5)}; fixed[("C",2,0)]=s
z,res,it=solve(fixed)
P=polys(z)
def rat(p): return sum(pari.bestappr(pari.polcoef(p,k),10**30)*X**k for k in range(int(pari.poldegree(p))+1))
C2=rat(P[("C",2)]); print("res",pari.precision(res,4),"C2 =",pari.factor(C2)); print("C1-C2:",pari.factor(C1-C2))
a1=P[("a",1)]**2; print("row1:",pari.factor(rat(a1)))
from algdeg import degof
for i in (0,2,3):
    d,p=degof(pari.polcoef(P[("a",i)]**2,4)/pari.polcoef(P[("a",i)]**2,0)); print("row",i,"field disc core",pari.core(pari.poldisc(p)))
