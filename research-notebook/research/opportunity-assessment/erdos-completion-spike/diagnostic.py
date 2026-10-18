#!/usr/bin/env python3
"""Finite diagnostics of the new component semantics; not a proof of an extremal bound."""
from itertools import combinations
from fractions import Fraction as F
from pathlib import Path
import json

def graph(n, edges):
    es={tuple(sorted(e)) for e in edges}
    def adj(u,v): return tuple(sorted((u,v))) in es
    def cost(S): return sum(u in S and v in S for u,v in es)
    def indep(S): return cost(S)==0
    def degree(S,u):return sum(adj(u,v) for v in S)
    return adj,cost,indep,degree
n=5; V=set(range(n)); pairs=list(combinations(range(n),2)); graphs=identities=heavy=0
for mask in range(1<<len(pairs)):
    es=[p for j,p in enumerate(pairs) if mask>>j&1]
    adj,cost,indep,degree=graph(n,es)
    if any(all(adj(u,v) for u,v in combinations(T,2)) for T in combinations(V,3)):continue
    graphs+=1
    for bm in range(1<<n):
        B={u for u in V if bm>>u&1}
        C={u for u in V if 2*degree(B,u)>len(B)}
        assert indep(C);heavy+=1
        other=sorted(V-B)
        for em in range(1<<len(other)):
            E={u for j,u in enumerate(other) if em>>j&1}
            if not indep(E):continue
            assert cost(B|E)==cost(B)+sum(degree(B,u) for u in E)
            identities+=1
# Nontrivial stopped Case 1 witness from the Petersen graph KG(5,2).
n=10; V=set(range(n)); labels=list(combinations(range(5),2))
es=[(u,v) for u,v in combinations(V,2) if not set(labels[u])&set(labels[v])]
adj,cost,indep,degree=graph(n,es)
A=B={0,1,2,3};C=set();D={4,5};v=3;E={4};S=B|E
assert not any(all(adj(u,v) for u,v in combinations(T,2)) for T in combinations(V,3))
assert max(len(T) for k in range(n+1) for T in combinations(V,k) if indep(T))==4
assert all(degree(B,u)>1 for u in V-B) # actual stopping threshold k*n=1
assert C=={u for u in V-B if 2*degree(B,u)>len(B)}
assert not B&D and len(D)==n-len(A)-len(B) and all(2*degree(B,u)<=len(B) for u in D)
assert E <= {u for u in D if adj(v,u)} and len(S)==n//2 and cost(S)==2
# Necessary-assumption negative controls.
_,costK,_,degreeK=graph(3,[(0,1),(0,2),(1,2)])
triangle_failure=costK({1,2})>costK(set())+sum(degreeK(set(),u)for u in {1,2})
_,costO,_,degreeO=graph(2,[(0,1)])
overlap_failure=costO({0,1})!=costO({0,1})+degreeO({0,1},0)
assert triangle_failure and overlap_failure
alpha=F(2,5); f=alpha*(F(1,2)-alpha)/2
left=f-alpha*(F(1,2)-alpha)/2; claimed_right=2*(alpha-F(3,8))**2
assert left==0 and claimed_right==F(1,800)
report={'scope':'Exact finite diagnostics; Lean theorems supply general proofs',
        'triangle_free_graphs_on_five_labeled_vertices':graphs,
        'independent_extension_identity_checks':identities,'heavy_set_checks':heavy,
        'petersen_witness':{'vertices':10,'edges':[list(e)for e in es],'maximum_independent_size':4,
          'B':sorted(B),'C':sorted(C),'D':sorted(D),'v':v,'E':sorted(E),'S':sorted(S),
          'cost':cost(S),'proved_branch_upper_bound':'2'},
        'negative_controls':{'triangle_free_omission_fails':triangle_failure,
                             'disjointness_omission_fails':overlap_failure},
        'paper_piecewise_identity_error':{'alpha':'2/5','left':str(left),
          'claimed_right':str(claimed_right),'impact':'Displayed equality must be restricted to first branch; required inequality remains valid.'}}
Path(__file__).with_name('diagnostic.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('petersen_witness',)},indent=2))
