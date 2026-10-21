from deform2 import pari
def degof(v, maxd=24):
    for deg in (1,2,3,4,6,8,12,16,24):
        if deg>maxd: break
        p=pari.algdep(v,deg)
        if p!=0 and abs(pari.subst(p,'x',v))<pari("1e-"+str(int(pari.default("realprecision"))-40)) and max(abs(c) for c in pari.Vec(p))<pari("1e80"):
            return int(pari.poldegree(p)), p
    return None, None
def report(P):
    out={}
    for i in range(7):
        a2=P[("a",i)]**2; v=pari.polcoef(a2,4)/pari.polcoef(a2,0) if pari.polcoef(a2,0)!=0 else pari.polcoef(a2,3)/pari.polcoef(a2,4)
        out[("row",i)]=degof(v)
    for j in range(7):
        c=P[("C",j)]
        if c==0: continue
        v=pari.polcoef(c,4)/pari.polcoef(c,0); out[("col",j)]=degof(v)
    return out
