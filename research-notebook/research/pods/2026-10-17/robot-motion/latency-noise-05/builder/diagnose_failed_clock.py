"""Reproduce the failed native-clock witness. No physical plant integration."""
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_right
import gzip,json
from make_references import state_at
from ruckig_checks import export,queried_state
HERE=Path(__file__).resolve().parent

def main():
    identity='sign_60ms__ruckig'
    schedule=next(x for x in json.loads((HERE/'reference-schedules.json').read_text())['schedules'] if x['case']=='sign_60ms' and x['method']=='ruckig')
    native=json.loads(gzip.decompress((HERE/'native'/(identity+'-output.json.gz')).read_bytes()))
    starts=[Q(x['start_exact']) for x in schedule['pieces']]
    candidates=[];maximum=[0.,0.,0.]
    for row in native['queries']:
        t=Q(row['time']);piece=schedule['pieces'][min(bisect_right(starts,t)-1,len(starts)-1)];reference=state_at(piece,t)
        errors=[abs(row[k]-value) for k,value in zip(['q','qv','qa'],reference[:3])]
        maximum=[max(x,y) for x,y in zip(maximum,errors)]
        candidates.append((errors[2],row,reference,piece))
    error,row,reference,piece=max(candidates,key=lambda x:x[0])
    index=max(i for i,x in enumerate(native['commits']) if x['time']<=row['time'])
    commit=native['commits'][index];elapsed=row['time']-commit['time']
    state=[commit[k] for k in ['current_p','current_v','current_a']]
    fresh=export(state,commit['target'],[elapsed],minimum_duration=0.)
    fresh_state=queried_state(fresh,elapsed)
    assert fresh_state==[row[k] for k in ['q','qv','qa']]
    (HERE/'failed-native-clock-plan.json').write_text(json.dumps(fresh,indent=2)+'\n')
    canonical=json.loads((HERE/'ruckig-primary-exports.json').read_text())[identity][index]
    native_roots=[(p['kind'],p.get('index'),field,p[field]) for p in fresh['phases'] if p['duration']>0 for field in ['start','end']]
    root=min(native_roots,key=lambda item:abs(elapsed-item[3]))
    failure={'status':'FAIL: native-clock acceleration comparison exceeds the fixed audit tolerance; limit not changed',
             'stream_method':identity,'limits_q_v_a':[1e-8,1e-8,1e-10],'maximum_abs_q_v_a':maximum,'witness_time_s':row['time'],'witness_time_exact_binary':str(Q(row['time'])),
             'native_sample':row,'canonical_reference_q_v_a_j_snap':reference,'canonical_piece':piece,
             'native_commit_index':index,'native_commit':commit,'canonical_commit':canonical['commit_rational'],
             'canonical_input_state':canonical['plan']['input']['state'],'native_input_state':state,
             'native_minus_canonical_input_state':[x-y for x,y in zip(state,canonical['plan']['input']['state'])],
             'elapsed_native_double':elapsed,'closest_native_phase_root':{'kind':root[0],'index':root[1],'field':root[2],'local_time':root[3],'distance_s':abs(elapsed-root[3])},
             'distance_to_canonical_phase_boundary_s':min(abs(float(Q(row['time'])-t)) for t in starts),
             'canonical_phase_duration_exact_s':str(Q(piece['end_exact'])-Q(piece['start_exact'])),
             'native_plan_duration_s':fresh['duration'],'canonical_plan_duration_s':canonical['plan']['duration'],
             'primary_metric_dependency':'The physical solver uses frozen reference-schedules.json, not native replay output. This later failed audit therefore does not alter any primary metric. The equivalence of that canonical profile interpretation to the alternative native absolute clock fails this strict tolerance here; its effect on another physical replay is not evaluated in this stopped batch.',
             'scope':'All 144 canonical cases were already complete. No physical case was added or rerun to diagnose this witness. The same recorded native replan input was exported once to expose phase boundaries.'}
    (HERE/'native-clock-failure.json').write_text(json.dumps(failure,indent=2)+'\n')
    print(json.dumps(failure,indent=2))
if __name__=='__main__':main()
