import sys
from tt import at, PQ, pari
from ratinterp import ratfit
pari.set_real_precision(400)
mode=sys.argv[1]
ts=[];vals={}
for k in list(range(-14,0))+list(range(1,15)):
    t=pari(k)*pari("1/7")
    t1,t2=(t,0) if mode=="t1" else ((t,t) if mode=="diag" else (t,2*t))
    z,res=at(t1,t2)
    for i in (0,2,3):
        P,Q,p=PQ(z,i)
        vals.setdefault(("P",i),[]).append(P); vals.setdefault(("Q",i),[]).append(Q)
    ts.append(t)
for key,v in vals.items():
    g=ratfit(ts,v)
    print(key, None if g is None else (pari.factor(pari.numerator(g)), pari.factor(pari.denominator(g)), pari.content(pari.numerator(g)), pari.content(pari.denominator(g))),flush=True)
