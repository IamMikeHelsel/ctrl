#!/usr/bin/env python3
"""Exact mathematical negative controls, not just malformed-file rejection."""
from fractions import Fraction as F
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
R=F(1293,50000); I=F(2,47)
c=F(7797,10000); x=F(2797,7797); y=F(5000,7797)
q=F(23311017818,51047928060481223)
j=F(2172228946875000,51047928060481223)
beta=F(6256019367,241832986336)
Q=F(3,2)*x*x-F(5,4)*x+F(9,32)
assert x+y==1 and 2*c*y==1 and q>=0 and j>=0 and q+j==I
assert beta==c*c*j==Q+q and beta>R
nonconcavity_gap=j-R*(4*y-1)
assert nonconcavity_gap>0

# The same scalar x,q,j are realized by a triangle-free six-cluster graph,
# yet its two designated independent clusters are an actual half of cost0.
weights=[x/2,2*q/x,x/2-2*q/x,y/2,2*j/y,y/2-2*j/y]
assert all(w>0 for w in weights) and sum(weights)==1
assert weights[0]*weights[1]==q and weights[3]*weights[4]==j
assert weights[0]+weights[3]==F(1,2)

# Failed broader-window tangent: its maximum is on the actual HIGH domain.
fy=F(50,79); fj=I; b=fy-F(1,2); mu=2*fj/fy
L=8*R*(fy-mu)-2*mu; C=fj-4*R*(fy-mu)**2-mu*mu
B=(fj-R)/b-L; S=B*B/4+L*mu-C; d=B/2
assert C<0 and S>0 and b<d<fy
phi=(fj-R)*d/b-d*d
assert phi-(C+L*(d-mu))==S
P=lambda cc:(R-I-F(17,32))*cc*cc+F(7,8)*cc+R-F(3,8)
assert P(F(79,100))>0

# Without triangle-freeness, neighborhood internal edges were double counted
# in s; the claimed candidate cost is then false. This exact triangle is a
# meaningful test of the hypothesis rather than a graph in the theorem class.
tw=[F(1,3)]*3; edges=[(0,1),(0,2),(1,2)]
td=F(2,3); ts=F(4,9); tj=F(1,3); tb=F(1,2)
z=[F(1),1-tb/td,1-tb/td]
actual=sum(tw[u]*tw[v]*z[u]*z[v] for u,v in edges)
claimed=tj-tb*ts/td
assert sum(w*p for w,p in zip(tw,z))==F(1,2)
assert claimed==0 and actual==F(1,16)>claimed

out={
 'passed':True,
 'old_scalar_only_fails':{'c':str(c),'x':str(x),'y':str(y),'q':str(q),
   'j':str(j),'beta':str(beta),'beta_minus_R':str(beta-R),
   'both_old_candidate_bounds_equal_beta':True},
 'global_concavity_fails':{'j_minus_R_4y_minus1':str(nonconcavity_gap),
   'upward_derivative_jump':str(nonconcavity_gap/(y-F(1,2)))},
 'density_realizability_is_not_objective_realizability':{
   'vertex_cluster_weights':[str(w) for w in weights],
   'support_edges':[[0,1],[3,4]],'independent_half_clusters':[0,3],
   'half_mass':'1/2','actual_minimum_half_cost':'0'},
 'broad_tangent_fails':{'c':'79/100','y':str(fy),'j':str(fj),'b':str(b),
   'violating_degree':str(d),'C':str(C),'S':str(S),'violation':str(S),
   'old_middle_margin':str(P(F(79,100))),
   'meaning':'This affine majorant fails. No graph counterexample is claimed.'},
 'triangle_hypothesis_negative':{'weights':['1/3']*3,'edges':edges,
   'profile':[str(a) for a in z],'mass':'1/2',
   'claimed_cost':str(claimed),'actual_cost':str(actual),
   'meaning':'The neighborhood cost identity fails if triangle-freeness is removed.'}
}
print(json.dumps(out,indent=2))
