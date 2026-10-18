#!/usr/bin/env python3
"""Formal polynomial identities; point values are separate sanity controls."""
from fractions import Fraction as F
from pathlib import Path
import json
N=6
class P(dict):
 def __init__(self,a=0): super().__init__({k:F(v) for k,v in a.items() if v} if isinstance(a,dict) else ({(0,)*N:F(a)} if a else {}))
 def __add__(self,o):
  r=dict(self)
  for k,v in P(o).items():r[k]=r.get(k,F(0))+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.items()})
 def __sub__(self,o):return self+-P(o)
 def __rsub__(self,o):return P(o)+-self
 def __mul__(self,o):
  r={}
  for k,v in self.items():
   for l,w in P(o).items():
    m=tuple(a+b for a,b in zip(k,l));r[m]=r.get(m,F(0))+v*w
  return P(r)
 __rmul__=__mul__
 def __pow__(self,n):
  r=P(1)
  for _ in range(n):r=r*self
  return r
R,y,j,mu,d,a=[P({tuple(int(i==k) for i in range(N)):1}) for k in range(N)]
L=8*R*(y-mu)-2*mu;C=j-4*R*(y-mu)**2-mu**2;B=a-L;T=F(1,4)*B*B+L*mu
assert j-4*R*(y-d)**2-d*d==C+L*(d-mu)-(4*R+1)*(d-mu)**2
assert a*d-d*d==T+L*(d-mu)-(d-F(1,2)*B)**2
rows=[]
for r,yy,jj in [(F(1293,50000),F(50,79),F(2,47)),(F(16,625),F(800,1259),F(2,47)*F(59,60)),(F(1,50),F(2,3),F(2,47))]:
 mm=2*jj/yy;ll=8*r*(yy-mm)-2*mm;cc=jj-4*r*(yy-mm)**2-mm*mm;bb=(jj-r)/(yy-F(1,2))-ll;tt=bb*bb/4+ll*mm
 rows.append({'R':str(r),'y':str(yy),'j':str(jj),'C':str(cc),'C_plus_S':str(tt),'S':str(tt-cc),'accepts':cc<=0 and tt<=0})
assert rows[0]['accepts'] and F(rows[0]['S'])>0
assert rows[1]['accepts'] and F(rows[1]['S'])>0
assert not rows[2]['accepts']
out={'passed':True,'identities':'Two exact identities in the polynomial ring Q[R,y,j,mu,d,a]; a later substitutes (j-R)/(y-1/2). No grid is used for identities.','point_controls':rows,'scope':'General sufficient implication reviewed in REPORT; no parameter cover or graph constant.'}
Path(__file__).with_name('identity-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
