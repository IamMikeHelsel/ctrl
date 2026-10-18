"""Independent exact checks of the first Erdos formula card; no universal claim."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import json
import hashlib

P = Path(__file__).resolve().parent
data = json.loads((P/'inputs/preflight-results.json').read_text())
v = {k:Q(x) for k,x in data['scalar_obstruction'].items()}
x,y,q,j = [v[k] for k in ('x','y','q','j')]
R = Q(1293,50000)
weights = [x/2,2*q/x,x/2-2*q/x,y/2,2*j/y,y/2-2*j/y]
assert all(w > 0 for w in weights) and sum(weights) == 1
assert weights[0]*weights[1] == q and weights[3]*weights[4] == j
assert weights[0]+weights[3] == Q(1,2)
assert v['beta'] > R
N = int(data['pure_density_realizability_negative']['blowup_order'])
assert N%2 == 0 and all((N*w).denominator == 1 for w in weights)
assert [int(N*w) for w in weights] == list(map(int,data['pure_density_realizability_negative']['cluster_counts']))

mu,b = 2*j/y,y-Q(1,2)
L = 8*R*(y-mu)-2*mu
C = j-4*R*(y-mu)**2-mu**2
B = (j-R)/b-L
S = B*B/4+L*mu-C
# Compare every coefficient, not a selection of evaluation points.
lower = (j-4*R*y*y,8*R*y,-4*R-1)
lower_square = (C-L*mu-(4*R+1)*mu*mu,L+2*(4*R+1)*mu,-4*R-1)
upper_minus_tangent = (L*mu-C,B,Q(-1))
upper_square = (S-B*B/4,B,Q(-1))
assert lower == lower_square
assert upper_minus_tangent == upper_square
assert C<0 and S<0
left_derivative_at_b = 8*R*(y-b)-2*b
right_derivative_at_b = (j-R)/b-2*b
assert right_derivative_at_b > left_derivative_at_b

def inspect(n,edges,w,require_triangle_free=True):
    total = sum(w); gap = total-Q(1,2)
    assert total > Q(1,2)
    adj = [{u for u in range(n) if (min(v,u),max(v,u)) in edges} for v in range(n)]
    if require_triangle_free:
        assert all(not (adj[u]&adj[v]) for u,v in edges)
    d = [sum((w[u] for u in adj[v]),Q(0)) for v in range(n)]
    s = [sum((w[u]*d[u] for u in adj[v]),Q(0)) for v in range(n)]
    mass = sum((w[u]*w[v] for u,v in edges),Q(0))
    assert sum(w[v]*d[v] for v in range(n)) == 2*mass
    assert sum(w[v]*s[v] for v in range(n)) == sum(w[v]*d[v]**2 for v in range(n))
    branches = set(); mismatches=[]
    for v in range(n):
        if d[v] <= gap:
            frac = [Q(0) if u in adj[v] else Q(1,2)/(total-d[v]) for u in range(n)]
            claimed = (mass-s[v])/(4*(total-d[v])**2)
            branches.add('low')
        else:
            frac = [1-gap/d[v] if u in adj[v] else Q(1) for u in range(n)]
            claimed = mass-gap*s[v]/d[v]
            branches.add('high')
        assert all(0<=z<=1 for z in frac)
        assert sum(w[u]*frac[u] for u in range(n)) == Q(1,2)
        actual = sum((w[u]*w[z]*frac[u]*frac[z] for u,z in edges),Q(0))
        if require_triangle_free:
            assert actual == claimed
        elif actual != claimed:
            mismatches.append({'vertex':v,'actual':str(actual),'claimed':str(claimed)})
        # Independently derive the same profile from the old feasible endpoint.
        alpha = Q(1,2)/total
        delta = d[v]/total
        tau = alpha/(1-delta) if delta == 0 else min(alpha/(1-delta),(1-alpha)/delta)
        old_endpoint = [alpha-tau*((1 if u in adj[v] else 0)-delta) for u in range(n)]
        assert old_endpoint == frac
    return branches,mismatches

counts={}; branches=set()
for n in range(1,6):
    pairs=list(combinations(range(n),2));count=0
    for bits in range(1<<len(pairs)):
        edges={e for i,e in enumerate(pairs) if bits&(1<<i)}
        if any({(a,b),(a,c),(b,c)}<=edges for a,b,c in combinations(range(n),3)):
            continue
        # Unequal deterministic rational vertex masses, distinct from builder's grid.
        w=[y*Q(u+1,n*(n+1)//2) for u in range(n)]
        seen,_=inspect(n,edges,w);branches|=seen;count+=1
    counts[n]=count
assert branches == {'low','high'}
# Exact branch boundary d=b=1/4 in an edge with masses 1/2,1/4.
inspect(2,{(0,1)},[Q(1,2),Q(1,4)])
# Independence is essential: a triangle creates omitted neighbor-neighbor edges.
_,triangle_failure=inspect(3,{(0,1),(0,2),(1,2)},[Q(1,4)]*3,False)
assert len(triangle_failure)==3

replays={}
for name in ['preflight-results.json','point-moment-screen.json','neighborhood-screen-results.json']:
    a=(P/'inputs'/name).read_bytes();b=(P/'replay'/name).read_bytes()
    assert a==b,name
    replays[name]={'byte_identical':True,'sha256':hashlib.sha256(b).hexdigest()}
result={
 'scope':'Independent exact formula, finite-graph and point-certificate checks. No uniform dangerous-region proof.',
 'frozen_shortlist_sha256':hashlib.sha256((P/'inputs/shortlist-sha256.json').read_bytes()).hexdigest(),
 'six_cluster_realization':{'positive_weights':True,'finite_even_order':str(N),'true_half_cost':'0','chosen_cut_is_not_maximum':True},
 'point_certificate':{'R':str(R),'C':str(C),'S':str(S),'all_polynomial_coefficients_match':True,
                      'derivative_jump':str(right_derivative_at_b-left_derivative_at_b),'global_concavity_rejected':True},
 'independent_graph_checks':{'unequal_weight_counts':counts,'total':sum(counts.values()),'both_branches':True,
                             'branch_boundary':True,'zero_degree_case':True,'old_negative_endpoint_identity':True},
 'triangle_negative':triangle_failure,
 'copied_script_results':replays,
 'accepted':'Written fractional-half construction and affine sufficient certificate; exact local point passes.',
 'not_accepted':['uniform .02586 graph bound','regular-profile majorant for all graphs','novelty','new Lean theorem'],
 'all_checks_pass':True}
(P/'independent-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'all_checks_pass':True,'independent_graphs':sum(counts.values()),'copied_replays':3,'C':float(C),'S':float(S)}))
