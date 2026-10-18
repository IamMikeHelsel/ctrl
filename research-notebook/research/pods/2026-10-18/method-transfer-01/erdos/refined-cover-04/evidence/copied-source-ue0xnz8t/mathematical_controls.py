#!/usr/bin/env python3
"""Exact identities, failed shortcuts, and semantic graph controls."""
from fractions import Fraction as F
import json
R=F(63,2500);I=F(2,47)
# Small rational polynomial ring. This checks identities coefficient by
# coefficient, not only by evaluating selected points.
N=6
class P:
 def __init__(self,v=0):self.terms=v if isinstance(v,dict) else ({(0,)*N:F(v)} if v else {})
 def __add__(self,o):
  o=pol(o);t=self.terms.copy()
  for k,v in o.terms.items():t[k]=t.get(k,0)+v
  return P({k:v for k,v in t.items() if v})
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.terms.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);t={}
  for a,v in self.terms.items():
   for b,w in o.terms.items():
    k=tuple(x+y for x,y in zip(a,b));t[k]=t.get(k,0)+v*w
  return P({k:v for k,v in t.items() if v})
 __rmul__=__mul__
 def __pow__(self,n):
  out=P(1)
  for _ in range(n):out=out*self
  return out

def pol(v):return v if isinstance(v,P) else P(v)
def variable(i):return P({tuple(1 if k==i else 0 for k in range(N)):F(1)})
y,m,d,r,j,B=map(variable,range(N));L=8*r*(y-m)-2*m;C=j-4*r*(y-m)**2-m**2
lower=j-4*r*(y-d)**2-d**2-(C+L*(d-m)-(4*r+1)*(d-m)**2)
T=B**2*F(1,4)+L*m
upper=(B+L)*d-d**2-(T+L*(d-m)-(d-B*F(1,2))**2)
assert not lower.terms and not upper.terms

def point(c,j):
 y=1/(2*c);b=y-F(1,2);m=4*c*j;L=8*R*(y-m)-2*m
 C=j-4*R*(y-m)**2-m*m;B=(j-R)/b-L;T=B*B/4+L*m
 x=1-y;Q=F(3,2)*x*x-F(5,4)*x+F(9,32) if c<=F(4,5) else x*(F(1,2)-x)/2
 return {'c':c,'j':j,'y':y,'b':b,'mu':m,'L':L,'C':C,'B':B,'S':T-C,'T':T,
         'd_star':B/2,'uniform':c*c*j,'completion':Q+I-j}

# The former S<=0 test fails at a relevant degree, but the refined test passes.
improved=point(F(4,5),F(1,25))
assert improved['C']<0 and improved['T']<0<improved['S']
assert improved['uniform']>R and improved['completion']>R
assert improved['b']<improved['d_star']<improved['y']
# The moment test alone is not global; completion supplies this exact point.
failed_moment=point(F(83,100),F(1,25))
assert failed_moment['C']>0 and failed_moment['T']>0
assert failed_moment['completion']<R
# The old combined bound cannot alone prove the target, even on scalar inputs.
c=F(4,5);x=F(3,8);Q=F(3,128);jold=(I+Q)/(1+c*c);qold=I-jold;beta=c*c*jold
assert qold>=0 and jold>=0 and qold+jold==I and beta==Q+qold and beta>R
AA=R+F(1,4)-I;EE=R+F(1,8)
disc=4*AA*EE-F(3,8)**2
assert disc<0

# Graph-level tests count each unordered edge once.
def graph(w,edges):
 y=sum(w);j=sum(w[u]*w[v] for u,v in edges)
 neigh=[set() for _ in w]
 for u,v in edges:neigh[u].add(v);neigh[v].add(u)
 d=[sum(w[u] for u in neigh[v]) for v in range(len(w))]
 s=[sum(w[u]*d[u] for u in neigh[v]) for v in range(len(w))]
 assert sum(w[v]*d[v] for v in range(len(w)))==2*j
 assert sum(w[v]*s[v] for v in range(len(w)))==sum(w[v]*d[v]**2 for v in range(len(w)))
 rows=[]
 for v in range(len(w)):
  b=y-F(1,2)
  if d[v]<=b:
   profile=[F(0) if u in neigh[v] else 1/(2*(y-d[v])) for u in range(len(w))]
   predicted=(j-s[v])/(4*(y-d[v])**2);branch='low'
  else:
   profile=[1-b/d[v] if u in neigh[v] else F(1) for u in range(len(w))]
   predicted=j-b*s[v]/d[v];branch='high'
  assert all(0<=z<=1 for z in profile)
  assert sum(w[u]*profile[u] for u in range(len(w)))==F(1,2)
  actual=sum(w[u]*w[t]*profile[u]*profile[t] for u,t in edges)
  rows.append({'vertex':v,'branch':branch,'d':d[v],'s':s[v],'profile':profile,'claimed_cost':predicted,'actual_cost':actual})
 return {'mass':y,'edge_mass':j,'weights':w,'edges':edges,'profiles':rows}

# Irregular three-cluster Y realizes the improved point's c and j exactly.
example=graph([F(1,5),F(1,5),F(9,40)],[(0,1)])
assert example['mass']==F(5,8) and example['edge_mass']==F(1,25)
assert all(z['claimed_cost']==z['actual_cost'] for z in example['profiles'])
assert min(z['actual_cost'] for z in example['profiles'])==F(3,200)<R
# Triangle: moment double-counting still holds, but neighborhood independence
# fails. The alleged cost0 is false; the actual feasible profile costs1/16.
triangle=graph([F(1,3)]*3,[(0,1),(0,2),(1,2)])
assert all(z['claimed_cost']==0 and z['actual_cost']==F(1,16)>R for z in triangle['profiles'])
# For degree0 the LOW branch is defined and no reciprocal degree occurs.
assert example['profiles'][2]['d']==0 and example['profiles'][2]['branch']=='low'
# At d=b>0 the profiles and costs agree algebraically for an independent N.
y=F(5,8);b=y-F(1,2);j=F(1,50);s=F(1,100)
assert (j-s)/(4*(y-b)**2)==j-b*s/b

out={'polynomial_identities':{'lower_zero_coefficients':len(lower.terms),'upper_zero_coefficients':len(upper.terms)},
     'refinement_needed_and_succeeds':improved,'moment_alone_fails_completion_succeeds':failed_moment,
     'old_scalar_only_obstruction':{'c':c,'x':x,'q':qold,'j':jold,'beta':beta,'gap':beta-R,
       'graph_optimum_claimed':False},'old_global_discriminant_shortcut':{'margin':disc,'fails':True},
     'irregular_triangle_free_example':example,'triangle_rejects_cost_formula':triangle,
     'degree_zero_and_join_boundary_controls':True,'scope':'Exact algebra and finite semantic controls; no extra target search; not Lean'}
def encode(v):
 if isinstance(v,F):return str(v)
 raise TypeError(type(v))
print(json.dumps(out,indent=2,default=encode))
