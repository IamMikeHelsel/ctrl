"""1-parameter deformation with C1 = Lagrange's C1 fixed, s = C2(0) free: exact data per s."""
import sys, json
from deform2 import solve, Z0, pari, polys
X=pari("x")
fixedC1={("C",1,k):Z0[("C",1,k)] for k in range(5)}
def rat(v): return pari.bestappr(v,10**40)
def data(s, zstart=None):
    f=dict(fixedC1); f[("C",2,0)]=pari(s)
    z,res,it=solve(f,z=zstart)
    P=polys(z)
    C2=[rat(pari.polcoef(P[("C",2)],k)) for k in range(5)]
    out={"s":str(s),"res":float(abs(res)) if res else 0.0,"C2":[str(c) for c in C2]}
    for (i,j) in [(0,4),(2,5),(3,6)]:
        vi=pari.polcoef(P[("a",i)]**2,4)/pari.polcoef(P[("a",i)]**2,0)
        vj=pari.polcoef(P[("a",j)]**2,4)/pari.polcoef(P[("a",j)]**2,0)
        out[f"T{i}"]=str(rat(vi+vj)); out[f"N{i}"]=str(rat(vi*vj))
    return out, z
if __name__=="__main__":
    res=[]; z=None
    s0=-9072
    for k in range(-30,31):
        if k==0: continue
        s=pari(s0)+pari(k)*pari("37/10")
        o,z=data(s,None)
        res.append(o); print(o["s"],o["res"],o["C2"],o["T0"][:40],flush=True)
    json.dump(res,open("sfam.json","w"))
