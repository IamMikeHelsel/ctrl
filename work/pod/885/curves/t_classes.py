import sys, itertools, math
def prod(l):
    r=1
    for x in l: r=r*x
    return r
from tt import at, PQ, pari
pari.set_real_precision(400)
cands={
 "64+t1":lambda a,b:64+a, "144+t2":lambda a,b:144+b,
 "L3":lambda a,b:2704-5*a+21*b,
 "A1":lambda a,b:1-a/pari(80)+b/pari(189),
 "A2":lambda a,b:1-a/pari(80)+25*b/pari(3024),
 "B1":lambda a,b:1-a/pari(125)+b/pari(189),
 "B2":lambda a,b:1-a/pari(125)+25*b/pari(3024),
}
names=list(cands)
for (t1,t2) in [(pari("3/7"),pari("5/11")),(pari("-2/3"),pari("7/5")),(pari("9/13"),pari("-4/9"))]:
    z,res=at(t1,t2)
    vals={k:f(t1,t2) for k,f in cands.items()}
    print("point",t1,t2,"res",pari.precision(res,3))
    for i in (0,2,3):
        P,Q,p=PQ(z,i)
        ok,sq=pari.issquare(Q),None
        if not pari.issquare(Q): print("  row",i,"Q not square"); continue
        rq=pari.sqrtint(pari.numerator(Q))/pari.sqrtint(pari.denominator(Q))
        for sgn in (1,-1):
            c=-P+2*sgn*rq
            found=[S for n in range(0,len(names)+1) for S in itertools.combinations(names,n) if pari.issquare(c*prod([vals[s] for s in S]) if S else c)]
            print("  row",i,"class",sgn,"=",found[:3])
