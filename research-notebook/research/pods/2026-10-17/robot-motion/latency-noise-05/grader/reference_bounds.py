#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import json,hashlib
H=Path(__file__).resolve().parent;B=H.parent/'builder'
source=B/'reference-schedules.json';before=hashlib.sha256(source.read_bytes()).hexdigest();schedules=json.loads(source.read_text())['schedules'];out=[]
def at(p,t,k):
 z=t-Q(p['start_exact']);d=[Q(p[x]) for x in ['p','v','a','jerk','snap']]
 return sum((d[i]*z**(i-k)/factorial(i-k) for i in range(k,5)),Q(0))
for s in schedules:
 if s['method'] not in ['ruckig','ruckig_min_08']:continue
 peaks=[Q(0)]*3;joins=[Q(0)]*3;last=None
 for p in s['pieces']:
  start=Q(p['start_exact']);end=Q(p['end_exact']);assert end>start;assert Q(p['snap'])==0
  points={start,end};j=Q(p['jerk'])
  if j:
   root=start-Q(p['a'])/j
   if start<=root<=end:points.add(root)
  for k in [1,2,3]:peaks[k-1]=max(peaks[k-1],*(abs(at(p,t,k)) for t in points))
  if last:
   for k in range(3):joins[k]=max(joins[k],abs(at(p,start,k)-at(last,start,k)))
  last=p
 out.append({'case':s['case'],'method':s['method'],'exact_executed_v_a_j_peaks':[str(v) for v in peaks],
             'executed_v_a_j_peaks':[float(v) for v in peaks],'exact_max_q_v_a_join_gaps':[str(v) for v in joins],
             'max_q_v_a_join_gaps':[float(v) for v in joins],'strict_exact_limits_pass':all(a<=b for a,b in zip(peaks,[Q(1,10),Q(1,2),Q(15,2)])),
             'exact_C2_joins':all(v==0 for v in joins)})
assert hashlib.sha256(source.read_bytes()).hexdigest()==before
(H/'reference-bounds.json').write_text(json.dumps({'schedule_sha256':before,'method':'Exact rational extrema for frozen executed cubic pieces; endpoint/linear-acceleration root check. Joins compared exactly. No propagation or control theorem inferred.','rows':out},indent=2)+'\n')
print(json.dumps(out,indent=2))
