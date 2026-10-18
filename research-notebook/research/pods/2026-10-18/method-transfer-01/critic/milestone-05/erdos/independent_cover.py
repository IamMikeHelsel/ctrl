#!/usr/bin/env python3
"""Independent expanded-polynomial Bernstein bounds and horizontal coverage.
Does not import any builder module or use stored interval enclosures.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json,copy
HERE=Path(__file__).resolve().parent
R=F(251,10000);I=F(2,47);A=F(767,1000);H=F(22,25)
class P(dict):
 def __init__(self,x=0):super().__init__({k:F(v) for k,v in x.items() if v} if isinstance(x,dict) else ({(0,0):F(x)} if x else {}))
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
    m=(k[0]+l[0],k[1]+l[1]);r[m]=r.get(m,F(0))+v*w
  return P(r)
 __rmul__=__mul__
 def __pow__(self,n):
  r=P(1)
  for _ in range(n):r=r*self
  return r
c=P({(1,0):1});j=P({(0,1):1})
# All expressions below have positive denominators on our rectangle.
# y, mu and L0 have common denominator c. a and L1 use c(1-c).
K=4*R+1
y_num=P(F(1,2));mu_num=4*c*c*j
L0num=8*R*(y_num-mu_num)-2*mu_num
anum=2*c*c*(j-R)
L1num=anum-2*mu_num*(1-c)
Dnum=L1num-L0num*(1-c)
Cnum=j*c*c-4*R*(y_num-mu_num)**2-mu_num**2
Hminnum=anum*mu_num-mu_num**2*(1-c)
# Low numerator denominator 4K c^2(1-c)^2.
# High numerator denominator 4 c^2(1-c)^2.
polys={}
for theta in [0,1]:
 low=4*K*Cnum*(1-c)**2+theta**2*Dnum**2
 high=4*Hminnum*(1-c)+(1-theta)**2*Dnum**2
 Lt=(1-theta)*L0num*(1-c)+theta*L1num
 direct_high=(anum-Lt)**2+4*Lt*mu_num*(1-c)
 assert high==direct_high
 polys[theta]=(low,high)

def bernstein_upper(poly,cs,js):
 lo,hi=cs;bot,top=js
 n=max(k[0] for k in poly);m=max(k[1] for k in poly)
 power={}
 for (p,q),v in poly.items():
  for i in range(p+1):
   for k in range(q+1):
    z=v*comb(p,i)*lo**(p-i)*(hi-lo)**i*comb(q,k)*bot**(q-k)*(top-bot)**k
    power[i,k]=power.get((i,k),F(0))+z
 coeffs=[]
 for a in range(n+1):
  for b in range(m+1):
   coeffs.append(sum((v*F(comb(a,i),comb(n,i))*F(comb(b,k),comb(m,k)) for (i,k),v in power.items() if i<=a and k<=b),F(0)))
 return max(coeffs)

def q(c0):
 x=1-1/(2*c0)
 return F(3,2)*x*x-F(5,4)*x+F(9,32) if c0<=F(4,5) else x*(F(1,2)-x)/2

def check(data):
 assert F(data['R'])==R and F(data['I'])==I
 leaves=[n for n in data['nodes'] if n['method']!='split']
 boxes=[];counts={};worstC=None;worstT=None;theta_counts={0:0,1:0}
 for n in leaves:
  cs=tuple(map(F,n['c']));js=tuple(map(F,n['j']));cl,cu=cs;jl,ju=js
  assert A<=cl<cu<=H and 0<=jl<ju<=I
  method=n['method'];counts[method]=counts.get(method,0)+1
  if method=='uniform':assert cu*cu*ju<=R
  elif method=='completion':assert cl>=F(3,4) and q(cl)+I-jl<=R
  else:
   assert method=='free_moment'
   theta=int(F(n['theta']));assert theta in [0,1] and F(n['theta'])==theta
   theta_counts[theta]+=1
   low,high=polys[theta]
   ubC=bernstein_upper(low,cs,js);ubT=bernstein_upper(high,cs,js)
   assert ubC<=0 and ubT<=0,(cs,js,ubC,ubT)
   worstC=ubC if worstC is None else max(worstC,ubC);worstT=ubT if worstT is None else max(worstT,ubT)
  boxes.append((cs,js))
 # Ignore tree links. Horizontal strips independently tile c at every j.
 cuts=sorted({a for cs,js in boxes for a in js});assert cuts[0]==0 and cuts[-1]==I
 for bot,top in zip(cuts,cuts[1:]):
  yy=(bot+top)/2;segments=sorted(cs for cs,js in boxes if js[0]<yy<js[1]);cursor=A
  for lo,hi in segments:assert lo==cursor and hi>lo;cursor=hi
  assert cursor==H
 # Include every horizontal grid boundary, permitting boundary overlaps.
 for yy in cuts:
  segments=sorted(cs for cs,js in boxes if js[0]<=yy<=js[1]);cursor=A
  for lo,hi in segments:assert lo<=cursor;cursor=max(cursor,hi)
  assert cursor==H
 area=sum(((cu-cl)*(ju-jl) for (cl,cu),(jl,ju) in boxes),F(0));assert area==(H-A)*I
 # Low exterior and high exterior from P(H)+P'(H)(c-H)+a(c-H)^2.
 aa=R+F(1,4)-I;dd=F(3,8);ee=R+F(1,8)
 margins={'low':R-I*A*A,'high_leading':aa,'high_at_H':aa*H*H-dd*H+ee,'high_derivative':2*aa*H-dd}
 assert all(v>0 for v in margins.values())
 return {'leaves':len(leaves),'method_counts':counts,'theta_counts':theta_counts,'horizontal_strips':len(cuts)-1,
 'all_horizontal_boundary_levels':len(cuts),'exact_area':str(area),
 'largest_Bernstein_low_numerator_upper':str(worstC),'largest_Bernstein_high_numerator_upper':str(worstT),
 'exterior_margins':{k:str(v) for k,v in margins.items()}}

def main():
 data=json.loads((HERE/'inputs/certificate.json').read_text());result=check(data)
 # Independent coverage negative: remove one interior leaf while leaving
 # all tree links/counts untouched; the independent horizontal tiling fails.
 bad=copy.deepcopy(data);idx=next(i for i,n in enumerate(bad['nodes']) if n['method']!='split');bad['nodes'].pop(idx)
 try:check(bad)
 except AssertionError:missing=True
 else:raise AssertionError('missing leaf accepted')
 # Wrong target is rejected before any proof is accepted.
 bad=copy.deepcopy(data);bad['R']='1/50'
 try:check(bad)
 except AssertionError:target=True
 else:raise AssertionError('wrong target accepted')
 out={'passed':True,'scope':'Independent exact polynomial bounds and horizontal domain coverage; not a Lean endpoint',
 'certificate':result,'independent_negatives':{'removed_leaf':missing,'changed_target':target}}
 (HERE/'independent-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
