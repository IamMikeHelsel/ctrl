"""Exact diagnostic, no claim about official kernel instruction scoring."""
import json,time
from pathlib import Path
B=Path(__file__).resolve().parent
MASK=(1<<32)-1
def mix(x):
    x=((x^(x>>16))*0x7feb352d)&MASK
    x=((x^(x>>15))*0x846ca68b)&MASK
    return (x^(x>>16))&MASK
def matrix(d,s):
    a=[]
    for i in range(d):
        if d<3: a.append([1]*d);continue
        k=mix(s^(i*0x9e3779b9)^0x85ebca6b)%(d-1)
        j=k if k<i else k+1
        k=mix(s^(i*0x9e3779b9)^0xc2b2ae35)%(d-2)
        lo,hi=sorted([i,j]);v=k if k<lo else k+1;v=v if v<hi else v+1
        assert len({i,j,v})==3
        a.append([int(c in (i,j,v)) for c in range(d)])
    return a
def count(a,sparse):
    d=len(a);rows=[[(j,v) for j,v in enumerate(row) if v] if sparse else list(enumerate(row)) for row in a]
    visits=entries=0
    def go(i,used):
        nonlocal visits,entries
        visits+=1
        if i==d:return 1
        z=0
        for j,v in rows[i]:
            entries+=1
            if v and not (used>>j)&1:z+=v*go(i+1,used|1<<j)
        return z
    t=time.perf_counter();value=go(0,0)
    return dict(value=value,recursive_calls=visits,entries_examined=entries,seconds=time.perf_counter()-t)
results=[]
for d in (6,12,16):
    for seed in (0,1,2,42,MASK):
        a=matrix(d,seed);baseline=count(a,False);sparse=count(a,True)
        assert baseline['value']==sparse['value']
        assert baseline['recursive_calls']==sparse['recursive_calls']
        assert baseline['entries_examined']*3==sparse['entries_examined']*d
        results.append(dict(dimension=d,seed=seed,packed=(d<<32)|seed,baseline=baseline,sparse=sparse))
(B/'permanent-probe.json').write_text(json.dumps({'scope':'Exact algorithm instrumentation in Python, not kernel instruction counts. Preprocessing scans d^2 entries once.','cases':results},indent=2)+'\n')
print(json.dumps(results[-5:],indent=2))
for name,expr in [('Baseline','permanentSpecN'),('Sparse','Submission.impl')]:
    text=['import Submission','set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option profiler true']
    for x in results:
        if x['seed']!=0:continue
        text.append(f"theorem test{x['dimension']} : {expr} {x['packed']} = {x['baseline']['value']} := by rfl")
    (B/'kernel-spike'/f'{name}Replay.lean').write_text('\n'.join(text)+'\n')
