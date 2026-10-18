"""Numerical parameter scout. No theorem, hardware, or interval-certification claim."""
import datetime
import hashlib
import itertools
import json
import math
import platform
from pathlib import Path

HERE=Path(__file__).resolve().parent
DEADLINE=datetime.datetime(2026,10,18,21,45,tzinfo=datetime.timezone.utc)

def evaluate(v0,A,T,b,k,X=0.0):
    V0=v0+A*T
    V=V0+(A+b)/k
    def vel(t):
        return V0-b*t+(A+b)/k*(-math.expm1(-k*t))
    def pos(t):
        u=k*t
        h2=sum((-u)**n/math.factorial(n+2) for n in range(15)) if abs(u)<.01 else (u+math.expm1(-u))/(u*u)
        return V0*t-b*t*t/2+(A+b)*t*t*h2
    if V0==0 and A==0:
        root=0.0
    else:
        lo,hi=0.0,V/b
        for _ in range(100):
            mid=(lo+hi)/2
            if vel(mid)>0:lo=mid
            else:hi=mid
        root=(lo+hi)/2
    pre=X+v0*T+A*T*T/2
    return {'v0':v0,'A':A,'T':T,'b':b,'k':k,'X':X,
            'post_peak_time':root,'total_horizon':T+root,
            'envelope_peak':pre+pos(root),'simple_bound':pre+V*V/(2*b),
            'velocity_residual':vel(root),
            'initial_zero_also_exists':V0==0,
            'scope':'binary64 envelope evaluation; not a certified root or physical trajectory'}

rows=[]
for v0,A,T,b,k in itertools.product([0.,.01,.1,.41,1.],[0.,.1,1.],[0.,.05,.5],[.1,1.2,10.,100.],[.1,1.,8.,100.]):
    if datetime.datetime.now(datetime.timezone.utc)>=DEADLINE:
        raise SystemExit('Hard research deadline reached')
    rows.append(evaluate(v0,A,T,b,k))
focus=evaluate(.41,.1,.05,1.2,8.,.001)
negative=evaluate(0.,.1,0.,1.2,8.)
assert negative['initial_zero_also_exists'] and negative['post_peak_time']>0
assert focus['envelope_peak']<.15<focus['simple_bound']
assert all(r['envelope_peak']<=r['simple_bound']+1e-10*max(1.,r['simple_bound']) for r in rows)
out={'executed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
     'machine':platform.machine(),'python':platform.python_version(),
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'cases':len(rows),'focus':focus,'nonunique_zero_control':negative,
     'all_rows':rows,'decision':'The exact envelope is worth certifying for the fixed15cm task. Grid success does not prove a universal result.'}
(HERE/'recovery-scout-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'cases':len(rows),'focus':focus,'nonunique_zero_control':negative},indent=2))
