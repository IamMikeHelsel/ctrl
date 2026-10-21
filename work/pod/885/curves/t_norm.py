import json
from sfam import data, pari
from ratinterp import ratfit
pari.set_real_precision(400)
rows={}
ts=[];vals={0:[],2:[],3:[],"P0":[]}
for k in list(range(-20,0))+list(range(1,21)):
    t=pari(k)*pari("37/10"); o,z=data(t-9072)
    for i in (0,2,3):
        al=z[("a",i,2)]
        p=pari.algdep(al,4)
        p=p/pari.pollead(p)
        assert pari.polcoef(p,1)==0 and pari.polcoef(p,3)==0, p
        vals[i].append(pari.polcoef(p,0))
        if i==0: vals["P0"].append(pari.polcoef(p,2))
    ts.append(t)
for i in (0,2,3,"P0"):
    g=ratfit([pari(t) for t in ts],vals[i])
    print(i, pari.factor(pari.numerator(g)), "/", pari.factor(pari.denominator(g)), "content", pari.content(pari.numerator(g)), pari.content(pari.denominator(g)))
