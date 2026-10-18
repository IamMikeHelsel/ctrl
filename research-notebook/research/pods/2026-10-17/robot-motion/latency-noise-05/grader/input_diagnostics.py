#!/usr/bin/env python3
"""Exact means of the already frozen finite packet inputs. No new cases."""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
H=Path(__file__).resolve().parent;B=H.parent/'builder'
manifest=json.loads((B/'pre-run-input-manifest.json').read_text())
assert all(hashlib.sha256((B/n).read_bytes()).hexdigest()==v for n,v in manifest['files'].items())
spec=json.loads((B/'packets.json').read_text());rows=[]
for c in spec['cases']:
    if c['id']=='persistent_goal':continue
    packets=c['packets'];duration=Q(packets[-1]['ready_s'])-Q(packets[0]['ready_s'])
    positive=negative=zero=area=Q(0)
    for a,b in zip(packets,packets[1:]):
        target=Q(a['target_m']);width=Q(b['ready_s'])-Q(a['ready_s']);area+=target*width
        if target>0:positive+=width
        elif target<0:negative+=width
        else:zero+=width
    arithmetic=sum((Q(p['target_m']) for p in packets[:-1]),Q(0))/len(packets[:-1])
    rows.append({'case':c['id'],'scope':'Noise episode from first ready time through the final zero packet; final zero has zero weight in this episode.',
      'duration_s':str(duration),'sample_arithmetic_mean_m':str(arithmetic),'time_weighted_mean_m':str(area/duration),'positive_target_duration_s':str(positive),'negative_target_duration_s':str(negative),'zero_target_duration_s':str(zero)})
irregular=next(r for r in rows if r['case']=='irregular_alternation')
assert irregular['time_weighted_mean_m']=='-1/2600' and irregular['positive_target_duration_s']=='8/25' and irregular['negative_target_duration_s']=='18/25'
out={'passed':True,'pre_run_input_manifest_sha256':hashlib.sha256((B/'pre-run-input-manifest.json').read_bytes()).hexdigest(),'cases':rows,
 'qualification':'Irregular alternation has zero sample mean but a negative time-weighted mean because sign and dwell duration correlate. It is not zero-mean-in-time noise.'}
(H/'input-diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
