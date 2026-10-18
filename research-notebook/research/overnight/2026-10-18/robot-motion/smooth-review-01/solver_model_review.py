"""Inspect the saved solver model and accepted raw candidate, without re-solving."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from datetime import datetime
import json

HERE=Path(__file__).resolve().parent;B=HERE.parent/'smooth-baseline-01'
def read(n):return json.loads((B/n).read_text())
r=read('n90_cap10mm.json');data=r['solver_state_mm'];N=r['N'];h=F(1,100)
q,v,a,j=[list(map(F,data[k])) for k in ['q','v','a','j']]
assert all(len(x)==91 for x in [q,v,a,j])
eq=[];ineq=[]
initial=[F(77,19200)*1000,F(23,480)*1000,F(5,16)*1000,F(-1250)]
eq += [q[0]-initial[0],v[0]-initial[1],a[0]-initial[2],j[0]-initial[3],q[-1],v[-1],a[-1],j[-1]]
limits=[F(999999,10000),F(4999999,10000),F(74999,10)]
upper=initial[0]+10-F(1,100000)
for i in range(N):
    eq += [a[i+1]-a[i]-h*(j[i]+j[i+1])/2,
           v[i+1]-v[i]-h*a[i]-h*h*(j[i]/3+j[i+1]/6),
           q[i+1]-q[i]-h*v[i]-h*h*a[i]/2-h**3*(j[i]/8+j[i+1]/24)]
    qp=[q[i],q[i]+h*v[i]/4,q[i]+h*v[i]/2+h*h*a[i]/12,q[i]+3*h*v[i]/4+h*h*a[i]/4+h**3*j[i]/24,q[i+1]]
    vp=[v[i],v[i]+h*a[i]/3,v[i]+2*h*a[i]/3+h*h*j[i]/6,v[i+1]]
    ap=[a[i],a[i]+h*j[i]/2,a[i+1]]
    jp=[j[i],j[i+1]]
    ineq += [x-upper for x in qp]
    for values,lim in zip([vp,ap,jp],limits):ineq += [abs(x)-lim for x in values]
objective=sum((h*(u*u+u*w+w*w)/3/F(7500)**2 for u,w in zip(j,j[1:])),F(0))
assert abs(float(objective)-r['normalized_objective'])<1e-15
maxeq=float(max(map(abs,eq)));maxineq=float(max(F(0),*ineq))
saved=r['max_solver_constraint_violation_mm_units']
assert abs(max(maxeq,maxineq)-saved)<1e-9
cases=read('solver-summary.json')['cases'];records=[read(c['case']+'.json') for c in cases]
start=read('protocol-freeze.json')['frozen_utc'];impl=read('implementation-freeze.json')['frozen_utc'];ref=read('reference-freeze.json')['frozen_utc']
assert datetime.fromisoformat(start)<datetime.fromisoformat(impl)<min(datetime.fromisoformat(x['started_utc']) for x in records)
assert max(datetime.fromisoformat(x['finished_utc']) for x in records)<datetime.fromisoformat(ref)
out={'status':'PASS','scope':'Saved accepted floating candidate and the frozen model only. No new optimizer call, no KKT/dual certificate, no optimum or infeasibility claim.','normalized_objective_recomputed':float(objective),'reported_normalized_objective':r['normalized_objective'],'raw_max_equality_residual_mm_units':maxeq,'raw_max_positive_inequality_residual_mm_units':maxineq,'reported_max_constraint_violation_mm_units':saved,'accepted_solver_seconds':r['solver_time_s'],'accepted_whole_attempt_seconds':r['elapsed_s'],'six_recorded_outcomes':dict(Counter(x['solver_status'] for x in records)),'raw_vectors_available_only_for_optimal':all(('solver_state_mm' in x)==(x['solver_status']=='optimal') for x in records),'chronology_provenance_check':True,'convexity_review':'Objective is a positive sum of squares in jerk nodes; all displayed constraints are affine or absolute-value convex constraints. This establishes the model class, not the accuracy of a numerical solver output.','latency_limit':'The accepted .11887738s solver time and .13767125s full attempt time are not charged to the scheduled .52s start. The simulated comparison is offline and assumes zero added planning latency. No real-time execution or deadline guarantee is inferred.'}
(HERE/'solver-model-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
