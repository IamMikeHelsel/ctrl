"""Builder finite cross-check. This does not replace the Lean proof or critic."""
from pathlib import Path
import json
B=Path(__file__).resolve().parent
subsets=[tuple(i for i in range(7) if mask & (1<<i)) for mask in range(128)]
index={t:k for k,t in enumerate(subsets)}
def negative(i, t):
    # Direct ordered wedge insertion or minus contraction.
    before=sum(j<i for j in t)
    if i in t:
        return (-1)**(before+1),tuple(j for j in t if j!=i)
    return (-1)**before,tuple(sorted(t+(i,)))
def actual_k(t):
    c=1
    for i in range(6,-1,-1):
        s,t=negative(i,t);c*=s
    return c,t
def dot(a,b):return sum(v*b.get(k,0) for k,v in a.items())
def apply(cols,x):
    out={}
    for c,v in x.items():
        for r,w in cols[c].items():out[r]=out.get(r,0)+v*w
    return {r:v for r,v in out.items() if v}
K=[];U=[];rows=[]
for j,t in enumerate(subsets):
    s,tc=actual_k(t);formula=(-1)**sum(7-i for i in t)
    assert tc==tuple(i for i in range(7) if i not in t)
    assert s==formula
    K.append({index[tc]:s})
    d=-1 if 0 in t else 1
    U.append({j:1,index[tc]:d*s})
    rows.append({'subset':t,'actual_sign':s,'complement':tc,'diagonal_sign':d})
KU=[apply(K,u) for u in U]
UT=[{j:U[j].get(i,0) for j in range(128) if U[j].get(i,0)} for i in range(128)]
checks=0
for i in range(128):
    for j in range(128):
        assert dot(U[i],U[j])==(2 if i==j else 0)
        assert dot(U[i],KU[j])==((2 if 0 not in subsets[j] else -2) if i==j else 0)
        assert dot(UT[i],UT[j])==(2 if i==j else 0)
        checks+=3
assert sum(0 not in t for t in subsets)==sum(0 in t for t in subsets)==64
null={0:1,127:-1};out=apply(K,null)
assert all(out.get(i,0)+null.get(i,0)==0 for i in range(128))
assert actual_k((0,))[0]==-1
report={'status':'PASS','boundary':'Builder exact finite cross-check only; independent review pending.',
 'basis_cases':128,'matrix_entry_checks':checks,'positive_count':64,'negative_count':64,
 'wrong_unsigned_complement_rejected':True,'omitting_D_has_nonzero_kernel':True,
 'unpaired_null_vector':null,'rows':rows}
(B/'exact-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))
