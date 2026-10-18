"""Exact coefficient checks in Q[a,b][W]/(W²+1); not a Lean proof."""
from fractions import Fraction as F
import json
from pathlib import Path

def add(p,q):
    r=p.copy()
    for k,v in q.items(): r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v}
def neg(p): return {k:-v for k,v in p.items()}
def mul(p,q):
    r={}
    for (a,b),v in p.items():
        for (c,d),w in q.items():
            k=(a+c,b+d); r[k]=r.get(k,0)+v*w
    return {k:v for k,v in r.items() if v}
def prod(x,y):
    return (add(mul(x[0],y[0]),neg(mul(x[1],y[1]))),add(mul(x[0],y[1]),mul(x[1],y[0])))
a={(1,0):1}; b={(0,1):1}
if prod((a,b),(a,b)) != ({(2,0):1,(0,2):-1},{(1,1):2}): raise RuntimeError('square identity failed')
if prod((a,b),(a,neg(b))) != ({(2,0):1,(0,2):1},{}): raise RuntimeError('inverse numerator failed')
examples=[]
for r in [F(1),F(2),F(1,2),F(3),F(2,3),F(-2)]:
    aa=(r*r+1)/(2*r); bb=(r*r-1)/(2*r); t=2*aa*bb
    if aa*aa-bb*bb != 1: raise RuntimeError('normalization failed')
    if (aa*aa+bb*bb)**2 != 1+t*t: raise RuntimeError('norm failed')
    examples.append(dict(r=str(r),a=str(aa),b=str(bb),t=str(t)))
result={'status':'PASS','scope':'Two symbolic polynomial identities and six exact rational examples; not a Lean theorem or full matrix test','examples':examples}
Path(__file__).with_name('congruence-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
