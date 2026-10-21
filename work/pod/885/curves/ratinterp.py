import json, sys
import cypari2
pari=cypari2.Pari(); pari.allocatemem(2*10**9)
def ratfit(ts, ys, maxdeg=24):
    n=len(ts)
    for D in range(0, maxdeg+1):
        for m in range(D,-1,-1):
            k=D-m
            if m+k+2 > n-3: continue
            rows=[]
            for t,y in zip(ts,ys):
                rows.append([t**i for i in range(m+1)]+[-y*t**i for i in range(k+1)])
            M=pari.matrix(n,m+k+2,[c for r in rows for c in r])
            K=pari.matker(M)
            if len(K)==1:
                v=K[0]; p=sum(v[i]*pari('t')**i for i in range(m+1)); q=sum(v[m+1+i]*pari('t')**i for i in range(k+1))
                g=p/q
                return g
    return None
if __name__=="__main__":
    d=json.load(open("sfam.json"))
    print(len(d),"samples")
    ts=[pari(o["s"])+9072 for o in d]
    for key in ["T0","N0","T2","N2","T3","N3"]:
        g=ratfit(ts,[pari(o[key]) for o in d])
        print(key, g if g is None else (pari.poldegree(pari.numerator(g),'t'),pari.poldegree(pari.denominator(g),'t')))
        if g is not None:
            print("   ",pari.factor(pari.numerator(g)),"/",pari.factor(pari.denominator(g)))
        globals()[key]=g
    for i in (0,2,3):
        T=globals()[f"T{i}"]; N=globals()[f"N{i}"]
        if T is not None and N is not None:
            disc=T**2-4*N
            print("disc",i, pari.factor(pari.numerator(disc)), "/", pari.factor(pari.denominator(disc)))
