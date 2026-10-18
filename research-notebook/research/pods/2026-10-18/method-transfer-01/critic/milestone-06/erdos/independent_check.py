#!/usr/bin/env python3
"""Reconstruct E6 from exact formulas; test finite vertices and half enumeration."""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
import json
p=Path(__file__).parent;data=json.loads((p/'inputs/results-development.json').read_text());saved=data['counterexample']
y=F(599,1000);x=1-y;I=F(2,47);R=F(1,40);j=F(5,48)*y*y;q=I-j
w=[F(1,20),20*q,x/2-F(1,20),x/2-20*q]+[y/24]*24
X=set(range(4));Y=set(range(4,28));left={0,2}|set(range(4,16));right=set(range(28))-left
E={(0,1)}|{(4+i,16+(i+t)%12) for i in range(12) for t in range(5)}|{(u,v) for u in [0,2] for v in range(16,28)}|{(u,v) for u in [1,3] for v in range(4,16)}
assert len(E)==109 and all(u<v for u,v in E) and all(a>0 for a in w) and sum(w)==1
assert list(map(F,saved['weights']))==w and {tuple(e) for e in saved['edges']}==E
assert all((u in left)!=(v in left) for u,v in E) and sum(w[v] for v in left)==F(1,2)
N=22560000;counts=[N*a for a in w];assert all(a.denominator==1 for a in counts)
counts=list(map(int,counts));assert counts==saved['finite_simple_blowup']['cluster_sizes'] and sum(counts)==N
adj=[{u for u in range(28) if tuple(sorted((u,v))) in E} for v in range(28)]
# Check one ACTUAL finite vertex, not only a whole support-cluster move.
margins=[]
for v in range(28):
 side=X if v in X else Y
 internal=sum(counts[u] for u in adj[v]&side);external=sum(counts[u] for u in adj[v]-side)
 assert external>internal
 margins.append(external-internal)
assert min(margins)==1707980
internal=sum(counts[u]*counts[v] for u,v in E if (u in X)==(v in X))
assert F(internal,N*N)==I
cost=lambda profile:sum(profile[u]*profile[v] for u,v in E)
mu=F(599,4800);b=y-F(1,2);Fv=j-b*mu
profiles=[]
for v in sorted(Y):
 neigh=adj[v]&Y;degree=sum(w[u] for u in neigh);second=sum(w[u]*sum(w[z] for z in adj[u]&Y) for u in neigh)
 assert degree==mu>b and second==mu*mu
 selected=[w[u]*(1-b/degree) if u in neigh else w[u] if u in Y else F(0) for u in range(28)]
 assert sum(selected)==F(1,2) and all(0<=selected[u]<=w[u] for u in range(28))
 assert cost(selected)==Fv
 profiles.append(cost(selected))
uniform=j/(4*y*y);completion=x*(F(1,2)-x)/2+q
assert min(uniform,completion,*profiles)==F(240199,9600000)>R
assert Fv<completion<uniform
# Two genuinely integral witnesses in the exact finite blowup.
for key,expected in [('true_fractional_half',F(0)),('true_Y_restricted_half',Fv)]:
 z=list(map(F,saved[key]['selected_masses']));assert sum(z)==F(1,2) and cost(z)==expected
 assert all(0<=z[v]<=w[v] and (z[v]*N).denominator==1 for v in range(28))
 assert sum(int(v*N) for v in z)==N//2
# Missing global optimality is a real defect: flipping all clusters toward
# the displayed coloring changes the internal cost from I to zero.
assert all((u in left)!=(v in left) for u,v in E)
# The completion algorithm may choose the displayed global color class even
# when it asks for a MAXIMUM independent set after deleting the X edge.
# A perfect matching exists without that edge: reserve equal slots in each Y
# cluster for opposite X vertices, then use the shift-zero Y matching.
reserve=(counts[0]+counts[2])//12
assert counts[0]+counts[2]==counts[1]+counts[3]==12*reserve
assert reserve==376940 and all(counts[v]>reserve for v in Y)
assert all((4+i,16+i) in E for i in range(12))
assert all(counts[4+i]-reserve==counts[16+i]-reserve==186120 for i in range(12))
# Complete cross links match the reserved slots; equal remaining clusters
# match via shift zero. This covers every finite vertex without edge (0,1).
# Independent half-slice endpoint enumeration for four uniform benchmark hosts.
# Choose the unique partial coordinate, and enumerate all full subsets directly.
def endpoint_min(n,edges):
 cap=F(1,n);best=None;witness=None
 for v in range(n):
  other=[i for i in range(n) if i!=v]
  for size in range(n):
   rem=F(1,2)-size*cap
   if not 0<=rem<=cap:continue
   for full in combinations(other,size):
    z=[cap if i in full else rem if i==v else F(0) for i in range(n)]
    val=sum(z[a]*z[b] for a,b in edges)
    if best is None or val<best:best=val;witness=z
 return best,witness
checks={}
for name in ['K2','C4','C5','Petersen']:
 host=next(h for h in data['hosts'] if h['name']==name);val,z=endpoint_min(host['n'],host['edges'])
 expected=F(0) if name in ['K2','C4'] else F(1,50)
 assert val==expected and sum(z)==F(1,2)
 checks[name]=str(val)
# At odd support size, pure full clusters cannot have half mass. C5's two
# nonadjacent full clusters have cost zero but mass 2/5, not a fractional half.
assert all(F(k,5)!=F(1,2) for k in range(6))
assert F(2,5)<F(1,2)
out={'passed':True,'implicit_finite_order':N,'edges_in_support':len(E),'minimum_single_finite_vertex_local_margin':min(margins),'internal_cost':str(F(internal,N*N)),'uniform':str(uniform),'completion_envelope':str(completion),'every_neighborhood_cost':str(Fv),'retained_gap':str(Fv-R),'global_half_optimum':'0','Y_restricted_optimum':str(Fv),'both_optimum_witnesses_integral_in_finite_blowup':True,'perfect_matching_without_X_edge':{'reserved_per_Y_cluster':reserve,'remaining_per_Y_cluster':186120,'consequence':'Global color class is a maximum independent set even after X-edge deletion.'},'independent_uniform_half_optima':checks,'odd_support_negative':'C5 has no all-full-cluster half; allowing only floor-half cluster mass would give a spurious zero value at mass 2/5. A partial cluster is necessary.','scope':'Exact written finite counterexample to retained local-cut envelope/profile test, not to all completion outputs or global cuts.'}
(p/'independent-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
