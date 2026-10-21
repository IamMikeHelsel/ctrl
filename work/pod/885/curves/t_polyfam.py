import sys
from families import pari, load
from polyrows import poly_rows
cases=[("chou4a",{"m":"2","q":"x","r":"1"}),("chou4a",{"m":"3","q":"x","r":"1"}),("chou4b",{"m":"2","q":"x","r":"1"}),("chou4b",{"m":"3","q":"x","r":"1"}),
("chou3",{"u1":"2","u2":"1","v1":"x","v2":"1"}),("chou3",{"u1":"3","u2":"1","v1":"x","v2":"1"}),("chou3",{"v1":"2","v2":"1","u1":"x","u2":"1"}),("chou3",{"v1":"3","v2":"1","u1":"x","u2":"1"}),("chou3",{"v1":"3","v2":"2","u1":"x","u2":"1"})]
for fam,subs in cases:
    U,V=load(fam,subs)
    for o,(A,B) in (("rows",(U,V)),("cols",(V,U))):
        for K in (2,4):
            R=poly_rows(B,K)
            known=[str(a) for a in A]
            new=[(sorted(s)) for k,(X,s) in R.items() if k not in known]
            facs=[[int(pari.poldegree(f)) for f in pari.factor(B[j]-B[0])[0]] for j in range(1,len(B))]
            print(fam,subs,o,"K",K,"known",sum(k in known for k in R),"new",new,"diff-factor-degs",facs,flush=True)
