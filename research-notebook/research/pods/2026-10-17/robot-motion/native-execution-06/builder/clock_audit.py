"""Summarize saved plan clock/duration metadata; no native or plant execution."""
from pathlib import Path
from fractions import Fraction as Q
import difflib,json
HERE=Path(__file__).resolve().parent
OLD=HERE.parents[1]/'latency-noise-05/builder'
exports=json.loads((HERE/'ruckig-primary-exports.json').read_text())
validation=json.loads((HERE/'ruckig-primary-validation.json').read_text())
rows=[];collapsed=[];offsets=[]
for identity,plans in exports.items():
    for plan in plans:
        offsets.append(abs(Q(plan['native_minus_scheduler_time_exact'])))
        x=plan['plan'];baseline=max(x['minimum_duration'],x['independent_minimum_duration'])
        rows.append({'stream_method':identity,'rational_commit':plan['commit_rational'],
                     'native_commit_exact':plan['native_commit_exact'],'minimum_duration':x['minimum_duration'],
                     'independent_minimum_duration':x['independent_minimum_duration'],'actual_duration':x['duration'],
                     'additional_blocked_adjustment':x['duration']-baseline})
        for phase in x['phases']:
            if phase['duration']>0 and phase['start']==phase['end']:
                absolute=Q(plan['native_commit_exact'])+Q(phase['start'])
                collapsed.append({'stream_method':identity,'commit':plan['commit_rational'],'phase':phase,
                                  'absolute_cumulative_time_exact':str(absolute),
                                  'before_next_commit_or_horizon':absolute<Q(plan['executed_until_rational'])})
result={'plans':len(rows),'rows':rows,'maximum_native_scheduler_offset_exact':str(max(offsets)),
        'maximum_native_scheduler_offset_s':float(max(offsets)), 'collapsed_positive_local_phases':collapsed,
        'pre_run_state_check_count':sum(len(v) for v in validation['cases'].values())}
(HERE/'clock-and-duration-audit.json').write_text(json.dumps(result,indent=2)+'\n')
text=''
for name in ['make_references.py','run_comparison.py','native_replay.cpp']:
    text+=''.join(difflib.unified_diff((OLD/name).read_text().splitlines(True),(HERE/name).read_text().splitlines(True),fromfile='frozen05/'+name,tofile='native06/'+name))
(HERE/'implementation-changes.diff').write_text(text)
old=json.loads((OLD/'reference-schedules.json').read_text())['schedules']
new=json.loads((HERE/'reference-schedules.json').read_text())['schedules']
oldmap={(x['case'],x['method']):x for x in old}
same=[x==oldmap[(x['case'],x['method'])] for x in new if x['method'] in ['raw','fir']]
assert len(same)==12 and all(same)
(HERE/'raw-fir-reference-equality.json').write_text(json.dumps({'passed':True,'unchanged_reference_schedules':12,
    'scope':'Entire raw and FIR schedule objects equal frozen05, including histories, coefficients, timing and admissions.'},indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
