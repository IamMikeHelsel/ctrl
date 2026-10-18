#!/usr/bin/env python3
"""Construct a fixed-target rational cover; no floating-point acceptance."""
from fractions import Fraction as F
from pathlib import Path
from datetime import datetime,timezone
import json,time,sys
HERE=Path(__file__).resolve().parent
R=F(251,10000); I=F(2,47); A=F(767,1000); H=F(22,25)
THETAS=[F(0),F(1)]
class IV:
 def __init__(self,lo,hi=None):self.lo=F(lo);self.hi=F(lo if hi is None else hi);assert self.lo<=self.hi
 def __add__(self,b):
  b=iv(b);return IV(self.lo+b.lo,self.hi+b.hi)
 __radd__=__add__
 def __neg__(self):return IV(-self.hi,-self.lo)
 def __sub__(self,b):return self+-iv(b)
 def __rsub__(self,b):return iv(b)+-self
 def __mul__(self,b):
  b=iv(b);v=[x*y for x in [self.lo,self.hi] for y in [b.lo,b.hi]];return IV(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,b):
  b=iv(b);assert b.lo>0 or b.hi<0;return self*IV(1/b.hi,1/b.lo)
 def __rtruediv__(self,b):return iv(b)/self
 def sq(self):return IV(0 if self.lo<=0<=self.hi else min(self.lo**2,self.hi**2),max(self.lo**2,self.hi**2))
 def pair(self):return [str(self.lo),str(self.hi)]
def iv(v):return v if isinstance(v,IV) else IV(v)
def q(c):
 x=1-1/(2*c)
 return F(3,2)*x*x-F(5,4)*x+F(9,32) if c<=F(4,5) else x*(F(1,2)-x)/2

def free_data(c,j):
 y=1/(2*c);mu=4*c*j;b=y-F(1,2);K=4*R+1
 L0=8*R*(y-mu)-2*mu
 C=j-4*R*(y-mu).sq()-mu.sq()
 a=(j-R)/b;L1=a-2*mu;D2=(L1-L0).sq();Hmin=a*mu-mu.sq()
 return C,D2,Hmin,K

def bounds(c,j):
 C,D2,Hmin,K=free_data(c,j)
 slopes=[]
 for theta in THETAS:
  low=C+theta*theta*D2/(4*K);high=Hmin+(1-theta)**2*D2/4
  slopes.append({'theta':str(theta),'low':low.pair(),'high':high.pair()})
 return {'uniform_upper':str(c.hi*c.hi*j.hi),
         'completion_upper':str(q(c.lo)+I-j.lo),'C':C.pair(),'D2':D2.pair(),
         'Hmin':Hmin.pair(),'slopes':slopes}

def accept(v):
 if F(v['uniform_upper'])<=R:return ('uniform',None)
 if F(v['completion_upper'])<=R:return ('completion',None)
 for s in v['slopes']:
  if F(s['low'][1])<=0 and F(s['high'][1])<=0:return ('free_moment',s['theta'])
 return None

nodes=[];leaves=[];failures=[];started=time.monotonic()
def cover(c,j,depth=0):
 idx=len(nodes);v=bounds(c,j);node={'c':c.pair(),'j':j.pair(),'depth':depth,'bounds':v};nodes.append(node)
 decision=accept(v)
 if decision:
  node['method'],node['theta']=decision;leaves.append(idx);return idx
 if depth>=28 or len(nodes)>=200000 or time.monotonic()-started>120:
  node['method']='unresolved';failures.append(idx);return idx
 # Split at the old Q branch once, then alternate exact midpoint partitions.
 if c.lo<F(4,5)<c.hi:axis='c';m=F(4,5)
 elif depth%2==0:axis='c';m=(c.lo+c.hi)/2
 else:axis='j';m=(j.lo+j.hi)/2
 node.update({'method':'split','axis':axis,'midpoint':str(m),'reason':'No interval test certifies this entire cell'})
 if axis=='c':children=[cover(IV(c.lo,m),j,depth+1),cover(IV(m,c.hi),j,depth+1)]
 else:children=[cover(c,IV(j.lo,m),depth+1),cover(c,IV(m,j.hi),depth+1)]
 node['children']=children
 return idx

cover(IV(A,H),IV(0,I))
AA=R+F(1,4)-I;DD=F(3,8);EE=R+F(1,8)
P=lambda c:AA*c*c-DD*c+EE
margins={'low_uniform':R-I*A*A,'upper_quadratic_at_H':P(H),'upper_quadratic_derivative_at_H':2*AA*H-DD,'upper_quadratic_leading':AA,'middle_completion_domain':A-F(3,4),'middle_denominator_c':A,'middle_denominator_one_minus_c':1-H}
assert all(v>0 for v in margins.values())
counts={k:sum(nodes[i]['method']==k for i in leaves) for k in ['uniform','completion','free_moment']}
output={'kind':'Exact rational .0251 free-slope cover; provisional written graph implication, not Lean','R':str(R),'I':str(I),'theta_menu':list(map(str,THETAS)),'rectangle':{'c':[str(A),str(H)],'j':['0',str(I)]},'analytic_margins':{k:str(v) for k,v in margins.items()},'nodes':nodes,'leaf_count':len(leaves),'method_counts':counts,'max_depth':max(n['depth'] for n in nodes),'unresolved_nodes':failures,'passed':not failures,'recorded_utc':datetime.now(timezone.utc).isoformat()}
name='certificate.json' if not failures else 'failed-attempt-'+datetime.now(timezone.utc).strftime('%H%M%S')+'.json'
(HERE/name).write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps({'passed':not failures,'file':name,'nodes':len(nodes),'leaves':len(leaves),'methods':counts,'theta_counts':{str(t):sum(nodes[i].get('theta')==str(t) for i in leaves) for t in THETAS},'max_depth':output['max_depth'],'seconds':time.monotonic()-started,'unresolved':failures[:5]},indent=2))
sys.exit(0 if not failures else 1)
