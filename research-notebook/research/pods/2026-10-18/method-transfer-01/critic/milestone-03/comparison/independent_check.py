#!/usr/bin/env python3
"""Independent rational Laurent-polynomial and closed-cover check."""
from fractions import Fraction as F
from pathlib import Path
import json
class P(dict):
 def __init__(self,v=0):
  super().__init__({k:F(x) for k,x in v.items() if x} if isinstance(v,dict) else ({0:F(v)} if v else {}))
 def __add__(self,o):
  o=P(o); r=dict(self)
  for k,v in o.items():r[k]=r.get(k,F(0))+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.items()})
 def __sub__(self,o):return self+-P(o)
 def __rsub__(self,o):return P(o)+-self
 def __mul__(self,o):
  o=P(o);r={}
  for k,v in self.items():
   for l,w in o.items():r[k+l]=r.get(k+l,F(0))+v*w
  return P(r)
 __rmul__=__mul__
 def __pow__(self,n):
  r=P(1)
  for _ in range(n):r=r*self
  return r
 def at(self,z):return sum((v*z**k for k,v in self.items()),F(0))
I=F(2,47);R=F(323,12500);a=F(779,1000);h=F(783,1000);c=P({1:1})
y=P({-1:F(1,2)});x=1-y
Q1=F(3,2)*x*x-F(5,4)*x+F(9,32)
Q2=x*(F(1,2)-x)*F(1,2)
P1=R*(1+c*c)-c*c*(I+Q1)
P2=R*(1+c*c)-c*c*(I+Q2)
assert P1==P({2:R-I-F(17,32),1:F(7,8),0:R-F(3,8)})
A=R+F(1,4)-I; D=F(3,8); E=R+F(1,8)
assert P2==P({2:A,1:-D,0:E})
# Entire middle interval: P minus its endpoint chord is positive.
left=h;right=F(4,5);slope=(P1.at(right)-P1.at(left))/(right-left)
chord=P(P1.at(left))+slope*(c-left)
assert P1-chord==(-P1[2])*(c-left)*(right-c)
# Entire upper interval, in fact all real c: complete the square.
assert 4*A*P2==(2*A*c-D)**2+(4*A*E-D*D)
# Saving normalized from probability on Y to probability on whole graph.
# mu = j/y^2 = 4 c^2 j. Compare coefficient of ell*j^3.
assert 4*(4*c*c)**3*y*y==64*c**4
# For 1/2<=c<=4/5, ell=c(1-c); above 4/5 ell=4(1-c)^2.
assert 4*(1-c)**2-c*(1-c)==(1-c)*(4-5*c)
# j-cap factorization: use polynomial variable j, hold coefficient symbol k.
j=c
assert (I**3-j**3)==(I-j)*(I*I+I*j+j*j)
assert 1-48*I*I>0
window=I*h*h-64*a**5*(1-h)*I**3
margins={'low':R-I*a*a,'window':R-window,'middle_left':P1.at(h),
 'middle_right':P1.at(F(4,5)),'concavity':-P1[2],
 'upper_leading':A,'upper_square_remainder':4*A*E-D*D,'j_cap':1-48*I*I}
assert all(v>0 for v in margins.values())
cover=[(F(1,2),a),(a,h),(h,F(4,5)),(F(4,5),F(1))]
assert cover[0][0]==F(1,2) and cover[-1][1]==1
assert all(l<r for l,r in cover) and all(cover[i][1]==cover[i+1][0] for i in range(3))
assert h>F(7797,10000)>F(3,4)
# Independent falsification: confusing directed edge sum with edgeMass doubles
# mu and multiplies the claimed cubic saving by eight. On the two-vertex edge
# with equal weights, true unordered mass is 1/4, directed sum 1/2.
edge_mass=F(1,4);ordered=F(1,2);ell=F(1,4)
assert 4*ell*ordered**3==8*(4*ell*edge_mass**3)
# At alpha=1/2, true constant profile cost is 1/16. The wrong saving 1/8
# would demand a negative cost, impossible for unit profiles and psi=0.
assert F(1,4)*edge_mass-4*ell*ordered**3<0
out={'passed':True,'method':'independent exact Laurent identities and rational interval margins',
 'identities':7,'cover':[[str(l),str(r)] for l,r in cover],
 'margins':{k:str(v) for k,v in margins.items()},
 'independent_negative':{'kind':'directed edge normalization overstates saving on actual K2',
 'true_edge_mass':str(edge_mass),'wrong_ordered_mass':str(ordered),
 'wrong_claimed_objective_upper':str(F(1,4)*edge_mass-4*ell*ordered**3),
 'rejected':True},'scope':'Arithmetic and written composition only; cited saving lemma not rebuilt here.'}
Path(__file__).with_name('independent-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
