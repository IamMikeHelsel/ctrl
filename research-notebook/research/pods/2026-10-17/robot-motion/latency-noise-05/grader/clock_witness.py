#!/usr/bin/env python3
"""Fresh per-plan witness for failed native clock, with unchanged limits."""
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_right
from math import factorial
import gzip, json, subprocess, hashlib
H=Path(__file__).resolve().parent;B=H.parent/'builder'
review=json.loads((H/'schedule-review.json').read_text())
exports=json.loads((B/'ruckig-primary-exports.json').read_text())
schedules={(s['case'],s['method']):s for s in json.loads((B/'reference-schedules.json').read_text())['schedules']}
results=[]
for key,check in review['native_clock'].items():
    if check['passed_fixed_state_limits']:continue
    name,method=key.split('__');minimum=.8 if method=='ruckig_min_08' else 0.
    with gzip.open(H/('native-'+key+'-output.json.gz'),'rt') as f:native=json.load(f)
    witness=check['worst_q_v_a'][2];t=witness['time'];i=bisect_right([r['time'] for r in native['commits']],t)-1
    commit=native['commits'][i];stored=exports[key][i];canonical=stored['plan']['input'];tau=Q(stored['commit_rational'])
    native_state=[commit[k] for k in ['current_p','current_v','current_a']]
    local_double=t-commit['time'];local_exact_binary=Q(t)-Q(commit['time']);local_canonical=Q(t)-tau
    queries=[local_double,float(local_canonical)]
    def run(state):
        args=[str(B/'.cache/ruckig_export')]+[format(float(x),'.17g') for x in [*state,commit['target'],minimum,*queries]]
        return json.loads(subprocess.check_output(args,text=True))
    canonical_plan=run(canonical['state']);native_plan=run(native_state)
    def plan_view(plan):
        positive=[p for p in plan['phases'] if p['duration']>0]
        def selected(elapsed):
            if elapsed>=plan['duration']:return plan['tail']
            return next(p for p in reversed(positive) if p['start']<=elapsed)
        return {'duration':plan['duration'],'phases':positive,'samples':plan['samples'],'selected_at_native_elapsed':selected(local_double),'selected_at_canonical_elapsed':selected(float(local_canonical))}
    schedule=schedules[name,method];starts=[Q(p['start_exact']) for p in schedule['pieces']]
    commit_differences=[]
    for k,(n,p) in enumerate(zip(native['commits'],exports[key])):
        ds=[n[f]-p['plan']['input']['state'][j] for j,f in enumerate(['current_p','current_v','current_a'])]
        commit_differences.append({'index':k,'time':n['time'],'native_minus_canonical_q_v_a':ds})
    away_witness=None
    for row in native['queries']:
        tt=Q(row['time']);distance=min(abs(tt-b) for b in starts)
        if distance<=Q(1,1000000):continue
        ix=max(0,min(bisect_right(starts,tt)-1,len(starts)-1));p=schedule['pieces'][ix];z=tt-starts[ix]
        canonical_a=float(Q(p['a'])+Q(p['jerk'])*z+Q(p['snap'])*z*z/2)
        d=abs(row['qa']-canonical_a)
        if away_witness is None or d>away_witness['acceleration_difference']:
            away_witness={'time':row['time'],'native':row['qa'],'canonical':canonical_a,'acceleration_difference':d,'nearest_canonical_boundary_distance':float(distance),'native_jerk':row['jerk'],'canonical_jerk':float(Q(p['jerk'])+Q(p['snap'])*z)}
    results.append({'key':key,'all_commit_state_differences':commit_differences,'largest_acceleration_difference_over_1us_from_canonical_boundary':away_witness,'fixed_acceleration_limit':1e-10,'witness':witness,'plan_index':i,'commit':commit,'canonical_input':canonical,
        'input_state_difference_native_minus_canonical':[a-b for a,b in zip(native_state,canonical['state'])],
        'native_local_double':local_double,'native_local_subtraction_exact_before_rounding':str(local_exact_binary),'canonical_local_exact':str(local_canonical),
        'native_minus_canonical_local_seconds':str(Q(local_double)-local_canonical),
        'canonical_plan_reexport':plan_view(canonical_plan),'native_plan_reexport':plan_view(native_plan)})
(H/'clock-witness.json').write_text(json.dumps({'failed_stream_count':len(results),'witnesses':results},indent=2)+'\n')
print(json.dumps([{'key':r['key'],'plan':r['plan_index'],'time':r['witness']['time'],'acceleration_difference':r['witness']['difference'],'input_state_difference':r['input_state_difference_native_minus_canonical']} for r in results],indent=2))
