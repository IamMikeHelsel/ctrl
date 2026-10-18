#!/usr/bin/env python3
"""Exact rational covering certificate. No floating-point acceptance decision."""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent
R=F(1293,50000);I=F(2,47);a=F(1559,2000);h=F(781,1000);c0=F(7797,10000);jlo=F(423,10000)
class IV:
 def __init__(self,lo,hi=None):self.lo=F(lo);self.hi=F(lo if hi is None else hi);assert self.lo<=self.hi
 def __add__(self,o):
  o=iv(o);return IV(self.lo+o.lo,self.hi+o.hi)
 __radd__=__add__
 def __neg__(self):return IV(-self.hi,-self.lo)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  o=iv(o);z=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return IV(min(z),max(z))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert o.lo>0 or o.hi<0
  return self*IV(1/o.hi,1/o.lo)
 def __rtruediv__(self,o):return iv(o)/self
 def sq(self):return IV(0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))
 def json(self):return [str(self.lo),str(self.hi)]
def iv(o):return o if isinstance(o,IV) else IV(o)
def point(y,j):
 mu=2*j/y;b=y-F(1,2);L=8*R*(y-mu)-2*mu;C=j-4*R*(y-mu)**2-mu**2;B=(j-R)/b-L;S=B*B/4+L*mu-C
 return dict(mu=mu,L=L,C=C,B=B,S=S)
def bounds(y,j):
 mu=2*j/y;b=y-F(1,2);L=8*R*(y-mu)-2*mu;C=j-4*R*(y-mu).sq()-mu.sq();B=(j-R)/b-L;S=B.sq()/4+L*mu-C
 return C,S
rootbox=(IV(F(500,781),F(1000,1559)),IV(jlo,I));nodes=[];leaves=[]
def cover(y,j,depth=0):
 C,S=bounds(y,j);idx=len(nodes);node={'y':y.json(),'j':j.json(),'C':C.json(),'S':S.json(),'depth':depth};nodes.append(node)
 if C.hi<0 and S.hi<=0:
  node['accepted']=True;leaves.append(idx);return idx
 assert depth<24,('unresolved',node)
 # Alternate axes; the complete child tree is part of the covering evidence.
 if depth%2==0:
  m=(y.lo+y.hi)/2;children=[cover(IV(y.lo,m),j,depth+1),cover(IV(m,y.hi),j,depth+1)];axis='y'
 else:
  m=(j.lo+j.hi)/2;children=[cover(y,IV(j.lo,m),depth+1),cover(y,IV(m,j.hi),depth+1)];axis='j'
 node.update({'accepted':False,'status':'interval enclosure inconclusive, subdivided','axis':axis,'midpoint':str(m),'children':children});return idx
cover(*rootbox)
# Independently traverse every partition edge and recompute enclosures.
seen=set()
def replay(idx,y,j):
 assert idx not in seen;seen.add(idx);n=nodes[idx];assert n['y']==y.json() and n['j']==j.json()
 C,S=bounds(y,j);assert n['C']==C.json() and n['S']==S.json()
 if n['accepted']:assert C.hi<0 and S.hi<=0;return
 mid=F(n['midpoint']);left,right=n['children']
 if n['axis']=='y':assert y.lo<mid<y.hi;replay(left,IV(y.lo,mid),j);replay(right,IV(mid,y.hi),j)
 else:assert j.lo<mid<j.hi;replay(left,y,IV(j.lo,mid));replay(right,y,IV(mid,j.hi))
replay(0,*rootbox);assert len(seen)==len(nodes)
P=lambda c:(R-I-F(17,32))*c*c+F(7,8)*c+R-F(3,8)
A=R+F(1,4)-I;B=F(3,8);D=R+F(1,8)
margins={'low_cap':R-I*a*a,'low_j':R-h*h*jlo,'middle_left':P(h),'middle_right':P(F(4,5)),'middle_concavity':-(R-I-F(17,32)),'upper_leading':A,'upper_discriminant':4*A*D-B*B,'old_threshold_gap':h-c0}
assert all(v>0 for v in margins.values())
# Preserve the failed broad window: the tangent really fails at this point,
# but the old middle branch already handles it, so no alternative route is used.
failed=point(F(50,79),I);assert failed['S']>0 and P(F(79,100))>0
out={'status':'exact arithmetic certificate, graph argument stated separately; not Lean','R':str(R),'I':str(I),'splits':{'c_low':str(a),'c_high':str(h),'j_low':str(jlo),'old_c0':str(c0)},'margins':{k:str(v) for k,v in margins.items()},'rectangle':{'y':rootbox[0].json(),'j':rootbox[1].json()},'cover':nodes,'leaf_count':len(leaves),'max_depth':max(n['depth'] for n in nodes),'largest_leaf_C_upper':str(max(F(nodes[i]['C'][1]) for i in leaves)),'largest_leaf_S_upper':str(max(F(nodes[i]['S'][1]) for i in leaves)),'failed_broad_window':{'c_interval':['1559/2000','79/100'],'witness_c':'79/100','witness_y':'50/79','witness_j':str(I),'point':{k:str(v) for k,v in failed.items()},'old_middle_margin':str(P(F(79,100))),'conclusion':'Fixed tangent fails on this broader window. The exact old bound already covers the failed point. Narrowed neighborhood window ends at781/1000.'}}
(HERE/'certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'leaves':len(leaves),'nodes':len(nodes),'max_depth':out['max_depth'],'worst_C':float(F(out['largest_leaf_C_upper'])),'worst_S':float(F(out['largest_leaf_S_upper']))},indent=2))
