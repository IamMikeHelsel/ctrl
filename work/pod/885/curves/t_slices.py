from fractions import Fraction as F
from math import gcd
from families import pari, load
from polyrows import poly_rows
vals=sorted({F(a,b) for a in range(1,13) for b in range(1,13) if gcd(a,b)==1 and F(a,b)!=1})
hits=0
for fam,var,fixed in [("chou3","u",("v1","v2")),("chou4a","q",("m",)),("chou4b","q",("m",))]:
    for t in vals:
        if fam=="chou3": subs={"v1":str(t.numerator),"v2":str(t.denominator),"u1":"x","u2":"1"}
        else: subs={"m":f"{t.numerator}/{t.denominator}","q":"x","r":"1"}
        try:
            U,V=load(fam,subs)
            if any(v==0 for v in V[1:]) or len(set(map(str,U)))<4: continue
            R=poly_rows(V,2); Cc=poly_rows(U,2)
        except Exception as e:
            continue
        nr=sum(k not in [str(a) for a in U] for k in R); nc=sum(k not in [str(b) for b in V] for k in Cc)
        if nr or nc:
            hits+=1; print("RICH",fam,subs,nr,nc,flush=True)
print("done hits",hits)
