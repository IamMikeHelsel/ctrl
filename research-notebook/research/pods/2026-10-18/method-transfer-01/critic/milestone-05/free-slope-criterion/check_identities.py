#!/usr/bin/env python3
"""Exact independent square identities and local control. No cover or graph search."""
from fractions import Fraction as F
from pathlib import Path
import json
N=8
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
R,y,j,mu,d,L,a,theta=[P({tuple(int(i==k) for i in range(N)):1}) for k in range(N)]
K=4*R+1; L0=8*R*(y-mu)-2*mu; C=j-4*R*(y-mu)**2-mu**2
low=j-4*R*(y-d)**2-d*d; high=a*d-d*d
assert 4*K*(low-L*(d-mu)) == 4*K*C+(L-L0)**2-(2*K*d-(8*R*y-L))**2
assert 4*(high-L*(d-mu)) == (a-L)**2+4*L*mu-(2*d-(a-L))**2
L1=a-2*mu; D=L1-L0; Lt=L0+theta*D
assert (Lt-L0)**2 == theta**2*D**2
assert (a-Lt)**2+4*Lt*mu == 4*(a*mu-mu**2)+(1-theta)**2*D**2
r=F(1,40); c=F(13,16); jj=F(28,705); yy=1/(2*c); mm=2*jj/yy
kk=4*r+1; aa=(jj-r)/(yy-F(1,2)); ll0=8*r*(yy-mm)-2*mm; ll1=aa-2*mm
cc=jj-4*r*(yy-mm)**2-mm*mm
h0=(aa-ll0)**2/4+ll0*mm; a1=cc+(ll1-ll0)**2/(4*kk); h1=(aa-ll1)**2/4+ll1*mm
assert cc<0<h0 and a1<0 and h1<0
scout=json.loads((Path(__file__).parent/'inputs/free-slope-scout-results.json').read_text())['local_exact_control']
assert [str(cc),str(h0),str(max(a1,h1))] == [scout['fixed_C'],scout['fixed_T'],scout['majorant']]
# Explicit semantic control: low branch alone does not certify the high branch.
dstar=(aa-ll0)/2
assert dstar>=yy-F(1,2)
high_gap=aa*dstar-dstar*dstar-ll0*(dstar-mm)
assert high_gap==h0>0
out={'passed':True,'formal_identities':4,'ring':'Q[R,y,j,mu,d,L,a,theta], denominators cleared; a is independent before substitution', 'local_control':{k:str(v) for k,v in {'R':r,'c':c,'j':jj,'y':yy,'mu':mm,'L0':ll0,'L1':ll1,'C':cc,'H_L0':h0,'A_L1':a1,'H_L1':h1,'high_branch_maximizer_L0':dstar}.items()},'negative_control':'C<0 alone fails the affine high-branch bound at d=(a-L0)/2, in the high branch','scope':'Generic sufficient algebra plus one local exact repair. No universal cover or graph-optimum claim. Whole numerical scout not replayed.'}
Path(__file__).with_name('identity-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
