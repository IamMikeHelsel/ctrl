#!/usr/bin/env python3
"""Independent exact boundary and scaling controls; not a graph proof."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
R=F(251,10000); I=F(2,47)
edges={(0,1),(1,2),(2,3),(3,4),(0,4)}
def cost(p,E=edges): return sum((p[u]*p[v] for u,v in E),F(0))
def edge_count(S): return sum(u in S and v in S for u,v in edges)
assert all(not all(tuple(sorted(e)) in edges for e in combinations(S,2)) for S in combinations(range(5),3))
pair_costs=[edge_count(S) for S in combinations(range(5),2)]
triple_costs=[edge_count(S) for S in combinations(range(5),3)]
assert min(pair_costs)==0 and min(triple_costs)==1>25*R
X={0,2};Y={1,3,4};q=F(edge_count(X),25);j=F(edge_count(Y),25)
c=F(5,2*len(Y));x=F(len(X),5)
def envelope(a,t):
 return F(3,2)*a*a-F(5,2)*a*t+F(9,8)*t*t if 4*a<=3*t else a*(t-a)/2
def completion(c):return envelope(1-F(1,2)/c,F(1,2))
assert q+j<=I and c*c*j>R and completion(c)+I-j<R
assert c==F(5,6) and completion(c)==F(1,50)
# The actual even construction must run on the 2-fold blowup, not odd C5.
assert envelope(F(4),F(5))==F(2)==100*completion(c)
assert F(2)<100*R
join=F(4,5);a=1-F(1,2)/join
assert a==F(3,8)
assert F(3,2)*a*a-F(5,4)*a+F(9,32)==a*(F(1,2)-a)/2==F(3,128)
assert completion(F(1))==0
assert I/2<R # min(j,I-j) is sufficient at the balanced endpoint.

# A nonconstant twin profile checks exact normalized descent with nonzero cost.
twins=[(F(1),F(0)),(F(1),F(1)),(F(0),F(0)),(F(1,2),F(1,2)),(F(1,2),F(1,2))]
avg=[sum(row)/2 for row in twins]
assert sum(avg)==F(5,2)
raw_blowup=sum((twins[u][i]*twins[v][j] for u,v in edges for i in range(2) for j in range(2)),F(0))
assert raw_blowup==4*cost(avg)==4
assert raw_blowup/100==cost(avg)/25==F(1,25)
assert raw_blowup/25!=cost(avg)/25

# Homogeneity sanity controls on both branches and their common boundary.
scales=[]
for a,t in [(F(1,3),F(1,2)),(F(3,8),F(1,2)),(F(2,5),F(1,2))]:
 for s in [F(2),F(7,3),F(10)]:
  assert envelope(s*a,s*t)==s*s*envelope(a,t)
  scales.append((str(s),str(a),str(t)))
out={'scope':'Exact controls only; no universal selector, graph endpoint or Lean acceptance',
 'cycle5':{'pair_min':min(pair_costs),'triple_min':min(triple_costs),'target_raw':str(25*R),'c':str(c),'j':str(j),'q':str(q),'U':str(c*c*j),'Q':str(completion(c)+I-j),'even_blowup_completion_raw':'2','even_blowup_target':str(100*R)},
 'balanced':{'c':'1','moment_denominator':'0','completion':'0','min_U_Q_upper':str(I/2),'R':str(R)},
 'join':{'c':'4/5','x':'3/8','completion':'3/128'},
 'nonconstant_blowup_profile':{'averages':[str(v) for v in avg],'raw_blowup':str(raw_blowup),'raw_original':str(cost(avg)),'normalized_both':'1/25','meets_R':False},
 'positive_scale_checks':scales,'all_checks_pass':True}
(Path(__file__).parent/'result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
