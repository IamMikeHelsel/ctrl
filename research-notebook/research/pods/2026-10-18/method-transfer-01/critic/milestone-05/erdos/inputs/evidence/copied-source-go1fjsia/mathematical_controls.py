#!/usr/bin/env python3
"""Exact free-slope identities, a .025 obstruction, and premise controls."""
from fractions import Fraction as F
import json
N=8
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

y,m,d,r,j,L,a,theta=map(variable,range(N))
K=4*r+1;L0=8*r*(y-m)-2*m;C=j-4*r*(y-m)**2-m**2
low=4*K*(j-4*r*(y-d)**2-d**2-L*(d-m)-C)-(L-L0)**2+(2*K*d-(8*r*y-L))**2
high=4*(a*d-d**2-L*(d-m))-((a-L)**2+4*L*m)+(2*d-(a-L))**2
L1=a-2*m;D2=(L1-L0)**2;Hmin=a*m-m*m;LL=L0+theta*(L1-L0)
interpolate_low=(LL-L0)**2-theta**2*D2
interpolate_high=(a-LL)**2+4*LL*m-4*Hmin-(1-theta)**2*D2
H_minimum=(a-L)**2+4*L*m-4*Hmin-(L-L1)**2
identities={'low_cleared_positive_4K':low,'high_cleared_4':high,
 'interpolated_low':interpolate_low,'interpolated_high':interpolate_high,
 'H_global_minimum':H_minimum}
assert all(not p.terms for p in identities.values())

def point(R,c,j):
 I=F(2,47);y=1/(2*c);b=y-F(1,2);mu=4*c*j;K=4*R+1;a=(j-R)/b
 L0=8*R*(y-mu)-2*mu;C=j-4*R*(y-mu)**2-mu**2;L1=a-2*mu;D2=(L1-L0)**2;Hmin=a*mu-mu*mu
 x=1-y;Q=F(3,2)*x*x-F(5,4)*x+F(9,32) if c<=F(4,5) else x*(F(1,2)-x)/2
 return {'R':R,'c':c,'j':j,'q':I-j,'x':x,'y':y,'b':b,'mu':mu,'K':K,'a':a,'C':C,
         'L0':L0,'L1':L1,'D2':D2,'theta0_low':C,'theta0_high':Hmin+D2/4,
         'theta1_low':C+D2/(4*K),'theta1_high':Hmin,'Hmin':Hmin,
         'fixed_high_vertex':(a-L0)/2,'uniform':c*c*j,'completion':Q+I-j,
         'high_phi_at_mean':a*mu-mu*mu,'constant_degree_profile_cost':j-b*mu}

repair=point(F(1,40),F(13,16),F(28,705))
assert repair['theta0_high']>0 and repair['theta0_low']<0
assert repair['theta1_low']<0 and repair['theta1_high']<0
assert repair['b']<repair['fixed_high_vertex']<repair['y']
assert repair['theta0_high']==F(37343401,1209560040000)
assert repair['theta1_high']==F(-1183,5964300)
assert repair['uniform']>repair['R'] and repair['completion']>repair['R']

benefit=point(F(251,10000),F(5347,6400),F(895,24064))
assert benefit['theta0_high']>0 and benefit['theta0_low']<0
assert benefit['theta1_low']<0 and benefit['theta1_high']<0
assert benefit['b']<benefit['fixed_high_vertex']<benefit['y']
assert benefit['uniform']>benefit['R'] and benefit['completion']>benefit['R']

obstruction=point(F(1,40),F(133,160),F(71,1880))
assert obstruction['j']==F(2,47)*F(213,240)
assert F(1,2)<obstruction['c']<1 and 0<obstruction['j']<F(2,47)
assert obstruction['Hmin']==F(1255919,50895360000)>0
assert obstruction['b']<obstruction['mu']<obstruction['y']
assert obstruction['uniform']-obstruction['R']==F(52719,48128000)>0
assert obstruction['completion']-obstruction['R']==F(97,8313830)>0
assert obstruction['high_phi_at_mean']==obstruction['Hmin']
assert obstruction['constant_degree_profile_cost']-obstruction['R']==obstruction['b']*obstruction['Hmin']/obstruction['mu']>0
# The exact one-point law is a feasible witness for the relaxed moment problem.
# It is not asserted to be an actual graph or its optimal fractional half.
mu=obstruction['mu'];j=obstruction['j'];y=obstruction['y'];b=obstruction['b']
assert mu==2*j/y and mu*mu<=j
moment_law={'support_degree':mu,'support_second_degree':mu*mu,'probability':F(1),
            'E_degree':mu,'E_second_degree':mu*mu,'E_degree_squared':mu*mu,
            'phi_expectation':obstruction['Hmin'],
            'asserted_graph_optimum':False}
# Exact triangle cost counter-control. Its neighborhood contains an edge.
w=[F(1,3)]*3;edges=[(0,1),(0,2),(1,2)];degree=F(2,3);second=F(4,9);mass=F(1)
profile=[F(1),F(1,4),F(1,4)];edge_mass=F(1,3)
actual=sum(w[u]*w[v]*profile[u]*profile[v] for u,v in edges)
false_cost=edge_mass-(mass-F(1,2))*second/degree
assert sum(w[u]*profile[u] for u in range(3))==F(1,2)
assert actual==F(1,16)>F(251,10000) and false_cost==0
assert sum(w[u]*second for u in range(3))==sum(w[u]*degree*degree for u in range(3))
# Slope/target false claims are rejected by exact inequalities, not tolerances.
assert not(obstruction['Hmin']<=0)
assert not(repair['theta0_high']<=0)
assert not(actual==false_cost)

out={'universal_polynomial_identities':{name:len(p.terms) for name,p in identities.items()},
 'known_theta1_repair_at_025':repair,'strict_benefit_at_target_0251':benefit,
 'global_affine_obstruction_at_025':obstruction,'relaxed_one_point_law':moment_law,
 'triangle_control':{'actual_profile':profile,'mass':F(1,2),'actual_cost':actual,'false_cost':false_cost,
                    'moment_identity_still_holds':True},
 'conclusions':['All five polynomial residuals have no nonzero coefficients.',
 'At the obstruction H(L)=Hmin+(L-L1)^2/4>0 for every real L.',
 'The obstructing mean lies in the high degree branch, so restriction to that branch does not repair an affine majorant.',
 'The obstruction is to the moment/global-affine proof route, not a counterexample graph or global half optimum.']}
def encode(v):
 if isinstance(v,F):return str(v)
 raise TypeError(type(v))
print(json.dumps(out,indent=2,default=encode))
