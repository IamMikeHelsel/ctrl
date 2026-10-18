#!/usr/bin/env python3
"""Independent exact FIR-only audit; no plant or new input runs."""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
SRC=HERE.parent.parent/'moving-goal-08/builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def kernel(n,z):return sum((-1)**k*comb(4,k)*max(z-k,F(0))**n for k in range(5))/factorial(n)
h=F(1,5);J=F(15,2)
def response(events,t,n):return sum(d*kernel(n,(t-s)/h)/h**(4-n) for s,d in events)
def extrema(events):
 knots=sorted({F(0)}|{s+k*h for s,d in events for k in range(5)})
 candidates=set(knots)
 for l,r in zip(knots,knots[1:]):
  jl,jr=response(events,l,1),response(events,r,1)
  if jl!=jr:
   root=l-jl*(r-l)/(jr-jl)
   if l<=root<=r:candidates.add(root)
 ap=max((abs(response(events,t,2)),t,response(events,t,2)) for t in candidates)
 jp=max((abs(response(events,t,1)),t,response(events,t,1)) for t in knots)
 return ap,jp
paths=['pre-run-input-manifest.json','protocol.txt','admission-transcripts.json','reference-extrema.json']
before={p:sha(SRC/p) for p in paths}
data=json.loads((SRC/'admission-transcripts.json').read_text());saved=json.loads((SRC/'reference-extrema.json').read_text())
rows=[]
for row in data['cases']:
 if row['method']!='fir':continue
 events=[];target=F(0);admissions=[]
 for o in row['outcomes']:
  delta=F(o['target_m'])-target
  assert delta==F(o['delta_m'])
  candidate=events+[(F(o['execution_s']),delta)]
  admission=F(o['admission_s'])
  knots=sorted({admission}|{s+k*h for s,d in candidate for k in range(5) if s+k*h>=admission})
  vals=[(t,response(candidate,t,1)) for t in knots]
  assert [[str(t),str(v)] for t,v in vals]==o['checked_knots']
  peak=max(abs(v) for t,v in vals)
  assert peak==F(o['candidate_future_jerk_peak'])
  accepted=peak<=J
  assert accepted==(o['outcome']=='accepted')
  if accepted:events=candidate;target=F(o['target_m'])
  admissions.append({'peak_jerk_m_s3':str(peak),'accepted':accepted})
 assert [[str(t),str(d)] for t,d in events]==row['events']
 a,j=extrema(events);comparison=saved[row['case']+'__fir']
 assert a[0]==F(comparison['exact_FIR_acceleration_peak'])
 assert j[0]==F(comparison['exact_FIR_jerk_peak'])
 rows.append({'case':row['case'],'admissions':admissions,'acceleration_peak_m_s2':str(a[0]),
  'acceleration_witness_time_s':str(a[1]),'acceleration_signed_m_s2':str(a[2]),
  'jerk_peak_m_s3':str(j[0]),'nominal_acceleration_pass':a[0]<=F(1,2)})
assert before=={p:sha(SRC/p) for p in paths}
out={'passed':True,'scope':'Independent exact FIR reference and admission audit only. Does not review native extrema, plant states, or final task results.',
 'sources':before,'cases':rows,'method':'Truncated-power sum, all knot jerk values, acceleration stationary points from exact affine-jerk zeroes.'}
(HERE/'reversal-reference-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
