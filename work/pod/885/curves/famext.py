"""Extend a 1-parameter 4x4 family (over Q(x)) by one row or column via the group law on a
triple curve, and compute the square-free part F(x) of the single remaining condition.
y^2 = F(x) has genus floor((deg F - 1)/2); deg F <= 4 means infinitely many 5x4 grids are possible.

usage: famext.py FAMILY "var=val,..." (one parameter left free, renamed x)
"""
import sys, json
from itertools import combinations, product
from families import pari, load

GP_DEFS = ['addP(a2,a4,P,Q)={ if(#P==1,return(Q)); if(#Q==1,return(P)); my(l); if(P[1]==Q[1], if(P[2]==-Q[2] || P[2]==0, return([0])); l=(3*P[1]^2+2*a2*P[1]+a4)/(2*P[2]), l=(Q[2]-P[2])/(Q[1]-P[1])); my(x3=l^2-a2-P[1]-Q[1]); [x3, -(P[2]+l*(x3-P[1]))]; }', 'negP(P)=if(#P==1,P,[P[1],-P[2]]);', 'mulP(a2,a4,P,n)={my(R=[0]); if(n<0,P=negP(P);n=-n); for(i=1,n,R=addP(a2,a4,R,P)); R}', 'msq(g)={my(h); if(!issquare(g,&h), error("nonsq")); h}', 'halfP(X,v)={my(s=vector(3,i,msq(X+v[i]))); [X+s[1]*s[2]+s[1]*s[3]+s[2]*s[3], (s[1]+s[2])*(s[1]+s[3])*(s[2]+s[3])]}', 'sqfree(g)={my(N=numerator(g)*denominator(g), f=factor(N), r=1, c=content(N)); N=N/c; f=factor(N); for(i=1,#f~, if(f[i,2]%2, r*=f[i,1])); [core(numerator(c)*denominator(c)), r]}']
for _d in GP_DEFS:
    pari(_d)
for _n in ('addP','mulP','halfP','sqfree','negP'):
    globals()['gp_'+_n] = pari(_n)



def run(U, V, label, box=1, maxterms=4, log=print):
    """New rows from triples of V; condition from the leftover column(s)."""
    res = []
    n = len(V)
    for T in combinations(range(n), 3):
        vs = [V[i] for i in T]
        others = [V[i] for i in range(n) if i not in T]
        a2 = vs[0] + vs[1] + vs[2]
        a4 = vs[0] * vs[1] + vs[0] * vs[2] + vs[1] * vs[2]
        vsv = pari(vs)
        H = [gp_halfP(u, vsv) for u in U]
        seen = set()
        for co in product(range(-box, box + 1), repeat=len(U)):
            nz = [c for c in co if c]
            if len(nz) < 2 or nz[0] < 0 or len(nz) > maxterms:
                continue
            P = pari("[0]")
            for c, h in zip(co, H):
                if c:
                    P = gp_addP(a2, a4, P, gp_mulP(a2, a4, h, c))
            if len(P) == 1:
                continue
            R = gp_addP(a2, a4, P, P)
            if len(R) == 1:
                continue
            X = R[0]
            key = str(X)
            if key in seen or any(X == u for u in U):
                continue
            seen.add(key)
            degs = []
            for vo in others:
                c0, F = gp_sqfree(X + vo)
                degs.append((int(pari.poldegree(F)), int(c0)))
            res.append((T, co, degs))
            if all(d <= 4 for d, _ in degs):
                log(f"LOWDEG {label} T={T} co={co} degs={degs} X={str(X)[:200]}")
    return res


if __name__ == "__main__":
    fam = sys.argv[1]
    subs = dict(kv.split("=") for kv in sys.argv[2].split(",")) if len(sys.argv) > 2 and sys.argv[2] else {}
    box = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    U, V = load(fam, subs)
    tag = f"{fam}[{sys.argv[2] if len(sys.argv) > 2 else ''}]"
    for orient, (A, B) in (("row", (U, V)), ("col", (V, U))):
        r = run(A, B, f"{tag}:{orient}", box=box)
        hist = {}
        for T, co, degs in r:
            for d, _ in degs:
                hist[d] = hist.get(d, 0) + 1
        print(f"{tag} {orient}: {len(r)} candidates; sqfree-degree histogram {sorted(hist.items())}", flush=True)
