#!/usr/bin/env python3
"""Exact independent slope, restricted-domain obstruction and quantifier controls."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
p=Path(__file__).parent
I=F(2,47)
def values(R,c,j):
 y=1/(2*c);x=1-y;b=y-F(1,2);mu=2*j/y;a=(j-R)/b;K=4*R+1
 L0=8*R*y-2*K*mu;L1=a-2*mu;C=j-4*R*(y-mu)**2-mu*mu
 def AH(L):return C+(L-L0)**2/(4*K),(a-L)**2/4+L*mu
 q=F(3,2)*x*x-F(5,4)*x+F(9,32) if x<=F(3,8) else x*(F(1,2)-x)/2
 return y,b,mu,a,C,L0,L1,AH,c*c*j,q+I-j
R=F(1,40);c=F(133,160);j=F(71,1880)
y,b,mu,a,C,L0,L1,AH,U,Q=values(R,c,j)
hmin=mu*(a-mu)
assert b<mu<y and hmin==F(1255919,50895360000)>0
assert U-R==F(52719,48128000) and Q-R==F(97,8313830)
assert mu*mu<=j and j-b*mu-R==F(3,150400)
# Identity H(L)=Hmin+(L-L1)^2/4 has coefficients: L^2/4+mu L-aL/2+a^2/4.
assert -L1/2==mu-a/2 and hmin+L1*L1/4==a*a/4
# A two-point moment-law control refutes vertex-dependent slope cancellation.
eps=F(1,100000);degrees=[mu-eps,mu+eps]
phis=[a*d-d*d for d in degrees]
assert all(b<d<y for d in degrees) and all(v>0 for v in phis)
slopes=[v/(d-mu) for d,v in zip(degrees,phis)]
assert all(v==L*(d-mu) for d,v,L in zip(degrees,phis,slopes))
assert sum(degrees)/2==mu and sum(phis)/2==hmin-eps*eps>0
# Exact .0251 matched benefit: same c,j and graph assumptions, changed slope only.
r1=F(251,10000);c1=F(5347,6400);j1=F(895,24064)
y1,b1,m1,a1,C1,l0,l1,ah,u1,q1=values(r1,c1,j1)
assert u1>r1 and q1>r1 and ah(l0)[0]<0<ah(l0)[1]
assert max(ah(l1))<0 and b1<(a1-l0)/2<y1
cert=json.loads((p/'inputs/certificate.json').read_text())
containing=[n for n in cert['nodes'] if n['method']!='split' and F(n['c'][0])<c1<F(n['c'][1]) and F(n['j'][0])<j1<F(n['j'][1])]
assert len(containing)==1 and containing[0]['method']=='free_moment' and containing[0]['theta']=='1'
cell=containing[0]
assert c1==sum(map(F,cell['c']))/2 and j1==sum(map(F,cell['j']))/2
# Alter the common slope in precisely this cell: actual midpoint disproves it,
# not merely a discrepancy from a stored enclosure.
wrong_gap=ah(l0)[1];assert wrong_gap>0
out={'passed':True,'obstruction':{'R':str(R),'c':str(c),'j':str(j),'mean':str(mu),'mean_minus_branch_boundary':str(mu-b),'y_minus_mean':str(y-mu),'phi_at_mean':str(hmin),'constant_degree_profile_gap':str(j-b*mu-R),'direct_uniform_gap':str(U-R),'direct_completion_gap':str(Q-R),'scope':'Every affine majorant with nonpositive mean fails at d=mu in the high branch; not a graph optimum.'},'matched_target_benefit':{'R':str(r1),'c':str(c1),'j':str(j1),'fixed_low':str(ah(l0)[0]),'fixed_high':str(wrong_gap),'free_low':str(ah(l1)[0]),'free_high':str(ah(l1)[1]),'actual_selected_cell':{'c':cell['c'],'j':cell['j'],'theta':cell['theta']},'wrong_slope_rejected_at_actual_cell_midpoint':True},'vertex_dependent_slope_negative':{'mean':str(mu),'degrees':list(map(str,degrees)),'phi_values':list(map(str,phis)),'slopes':list(map(str,slopes)),'expectation_phi':str(sum(phis)/2),'conclusion':'Each point can satisfy phi=L_v(d-mu), yet expectation is positive. L must be common across vertices.'}}
(p/'semantic-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
