#!/usr/bin/env python3
"""Exact preflight screens. No external packages, graph-conjecture claim, or optimizer."""
from fractions import Fraction as F
from pathlib import Path
from math import lcm
from itertools import combinations
import json,hashlib
HERE=Path(__file__).resolve().parent
c=F(7797,10000);x=1-1/(2*c);y=1-x;I=F(2,47)
Q=3*x*x/2-5*x/4+F(9,32);beta=c*c*(I+Q)/(1+c*c);q=beta-Q;j=I-q
assert beta>F(2586,100000) and q>=0 and j>=0
# A rational six-cluster triangle-free graph realizes x,q,j exactly.
weights=[x/2,2*q/x,x/2-2*q/x,y/2,2*j/y,y/2-2*j/y]
edges=[(0,1),(3,4)];X={0,1,2};half={0,3}
assert all(w>=0 for w in weights) and sum(weights)==1
assert sum(weights[i] for i in X)==x
assert weights[0]*weights[1]==q and weights[3]*weights[4]==j
assert sum(weights[i] for i in half)==F(1,2)
assert all(not(a in half and b in half) for a,b in edges)
N=lcm(2,*(w.denominator for w in weights));counts=[int(w*N) for w in weights]
assert sum(counts)==N and sum(counts[i] for i in half)*2==N
assert counts[0]*counts[1]==q*N*N and counts[3]*counts[4]==j*N*N
# C4: identical one-vertex means and exact half size, different edge moments.
E={(0,1),(1,2),(2,3),(0,3)}
laws={'bipartition':{(0,2):F(1,2),(1,3):F(1,2)},'adjacent_pairs':{e:F(1,4) for e in E},'uniform_halves':{e:F(1,6) for e in combinations(range(4),2)}}
couplings={}
for name,law in laws.items():
 marg=[sum(p for s,p in law.items() if i in s) for i in range(4)]
 cost=sum(p*sum(a in s and b in s for a,b in E) for s,p in law.items())
 assert marg==[F(1,2)]*4
 cov=[[sum(p for s,p in law.items() if a in s and b in s)-marg[a]*marg[b] for b in range(4)] for a in range(4)]
 assert all(sum(row)==0 for row in cov)
 assert sum(cov[i][i] for i in range(4))==1
 couplings[name]={'support':{','.join(map(str,s)):str(v) for s,v in law.items()},'marginals':list(map(str,marg)),'edge_cost':str(cost),'normalized_edge_cost':str(cost/16),'covariance':[[str(v) for v in row] for row in cov]}
# Neighborhood construction at the regular local profile, not an asserted graph.
b=y-F(1,2);d=2*j/y;s=d*d
assert d<b
candidate=F(1,4)*(j-s)/(y-d)**2
assert candidate <F(2586,100000)
result={'scope':'Exact arithmetic screens; neither graph bound nor novelty claim',
 'scalar_obstruction':{k:str(v) for k,v in dict(c=c,x=x,y=y,I=I,Q=Q,beta=beta,q=q,j=j).items()},
 'pure_density_realizability_negative':{'weights':list(map(str,weights)),'support_edges':edges,'X_clusters':sorted(X),'half_clusters':sorted(half),'blowup_order':str(N),'cluster_counts':list(map(str,counts)),'half_cost':'0','all_cut_internal_cost':str(q+j),'true_min_cut_internal_cost':'0','conclusion':'The density coordinates x,q,j ARE realized by an explicit rational triangle-free blowup. The scalar beta is NOT its actual minimum half cost. Graph realizability of x,q,j alone cannot exclude the obstruction. Max-cut optimality excludes this particular realization.'},
 'marginal_entropy_covariance_negative':{'host':'C4','laws':couplings,'conclusion':'Equal marginals, exact half cardinality, zero covariance row sums and equal covariance trace do not determine the edge cost. Maximum entropy alone need not minimize edge cost.'},
 'regular_neighborhood_screen':{'assumption':'hypothetical regular larger-side profile only; irregular case not proved','degree':str(d),'deletion_mass':str(b),'cost':str(candidate),'cost_decimal':float(candidate),'baseline':str(beta),'saving':str(beta-candidate)},
 'not_claimed':['counterexample to Erdos128','graph realizes scalar beta as optimum','general irregular-neighborhood inequality','Lean proof','source theorem transferred unchanged']}
(HERE/'preflight-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'checks':'passed','blowup_order_digits':len(str(N)),'regular_candidate':float(candidate),'scalar_baseline':float(beta),'C4_costs':{n:d['edge_cost'] for n,d in couplings.items()}},indent=2))
