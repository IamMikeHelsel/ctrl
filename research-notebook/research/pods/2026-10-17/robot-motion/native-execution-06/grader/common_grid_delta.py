#!/usr/bin/env python3
"""Saved physical-state differences at shared .5ms times; no new simulation.
Acceptance still depends on independent all-row replays of both saved datasets.
"""
from pathlib import Path
from fractions import Fraction as Q
import csv,gzip,json
H=Path(__file__).resolve().parent;B=H.parent/'builder';OLD=H.parents[1]/'latency-noise-05/builder'
metrics=json.loads((B/'metrics.json').read_text())['rows'];rows=[]
def read(path):
 out={}
 with gzip.open(path,'rt') as f:
  for r in csv.DictReader(f):
   t=Q(r['time_exact'])
   if (t*2000).denominator==1 and r['side']!='left':out[t]=[float(r[k]) for k in ['x','v','a']]
 return out
for m in metrics:
 if m['sample_step_s']!=.0005 or m['method'] not in ['ruckig','ruckig_min_08']:continue
 stem=f"{m['case']}__{m['method']}__r{m['rate']}__w{int(m['disturbance']*100):02d}__dt500us"
 a=read(OLD/'traces'/(stem+'.csv.gz'));b=read(B/'traces'/(stem+'.csv.gz'));assert a.keys()==b.keys()
 maxima=[0.]*3;witness=[None]*3
 for t in a:
  for k in range(3):
   d=abs(b[t][k]-a[t][k])
   if d>maxima[k]:maxima[k]=d;witness[k]={'time_exact':str(t),'old05':a[t][k],'new06':b[t][k],'abs_difference':d}
 rows.append({'case_id':stem,'common_grid_samples':len(a),'max_abs_x_v_a_changes':maxima,'witness_x_v_a':witness})
assert len(rows)==72
result={'scope':'72 native-method parameter cases, shared exact-rational .5ms grid only. Saved physical states; continuous across reference events. Not an all-time bound. Native jerk/command branch equivalence is not inferred.','rows':rows,'total_common_samples':sum(x['common_grid_samples'] for x in rows),'max_abs_x_v_a_changes':[max(x['max_abs_x_v_a_changes'][k] for x in rows) for k in range(3)]}
(H/'common-grid-delta.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
