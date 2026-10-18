"""Finite pre-run state checks against a separate native retained-history driver."""
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_right
import gzip,json,math,subprocess
from make_references import state_at
HERE=Path(__file__).resolve().parent
LIMITS=[1e-8,1e-8,1e-10]
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
def main():
    schedules=json.loads((HERE/'reference-schedules.json').read_text())['schedules']
    exports=json.loads((HERE/'ruckig-primary-exports.json').read_text())
    validation=json.loads((HERE/'ruckig-primary-validation.json').read_text())
    assert validation['passed'] and sum(len(v) for v in validation['cases'].values())==16
    folder=HERE/'native-checks';folder.mkdir(exist_ok=True)
    results=[]
    for schedule in schedules:
        if schedule['method'] not in ['ruckig','ruckig_min_08']:continue
        identity=schedule['case']+'__'+schedule['method'];plans=exports[identity]
        minimum=.8 if schedule['method']=='ruckig_min_08' else 0.
        commits=[(x['native_commit_float'],x['plan']['input']['target']) for x in plans]
        horizon=schedule['horizon'];queries={i/2000 for i in range(round(horizon*2000)+1)}
        events=[float(Q(x['time_exact'])) for x in schedule['common_events']]
        events += [p[k] for p in schedule['pieces'] for k in ['start','end']]
        for t in events:
            queries.add(t)
            if t>0:queries.add(math.nextafter(t,-math.inf))
            if 0<t<horizon:queries.add(math.nextafter(t,math.inf))
        queries=sorted(t for t in queries if 0<=t<=horizon)
        inputs=str(len(commits))+'\n'+''.join(f'{t:.17g} {target:.17g}\n' for t,target in commits)+str(len(queries))+'\n'+''.join(f'{t:.17g}\n' for t in queries)
        (folder/(identity+'-input.txt')).write_text(inputs)
        result=subprocess.run([str(HERE/'.cache/native_replay'),str(minimum)],input=inputs,text=True,capture_output=True,check=True)
        native=json.loads(result.stdout)
        (folder/(identity+'-output.json.gz')).write_bytes(gzip.compress(result.stdout.encode(),mtime=0))
        assert [x['time'] for x in native['queries']]==queries
        starts=[Q(x['start_exact']) for x in schedule['pieces']];residual=[0.,0.,0.];branches=[];worst=[None,None,None]
        for sample in native['queries']:
            t=Q(sample['time']);piece=schedule['pieces'][min(bisect_right(starts,t)-1,len(starts)-1)]
            reference=state_at(piece,t)
            for i,(name,value) in enumerate(zip(['q','qv','qa'],reference[:3])):
                error=abs(sample[name]-value)
                if error>residual[i]:residual[i]=error;worst[i]={'sample':sample,'canonical':reference,'piece':piece,'time_exact_binary':str(t)}
            if abs(sample['jerk']-reference[3])>1e-8:
                branches.append({'time_s':sample['time'],'native_jerk':sample['jerk'],'polynomial_jerk':reference[3],'nearest_polynomial_boundary_s':min(abs(float(t-s)) for s in starts)})
        current=[0.,0.,0.];exact_inputs=True
        assert len(plans)==len(native['commits'])
        for plan,commit in zip(plans,native['commits']):
            for i,(value,name) in enumerate(zip(plan['plan']['input']['state'],['current_p','current_v','current_a'])):
                current[i]=max(current[i],abs(value-commit[name]));exact_inputs &= value==commit[name]
            exact_inputs &= plan['native_commit_float']==commit['time'] and plan['plan']['duration']==commit['duration']
        passed=exact_inputs and all(v<=limit for v,limit in zip(residual,LIMITS))
        row={'stream_method':identity,'passed':passed,'queries':len(queries),'commits':len(commits),
             'reference_max_abs_q_v_a':residual,'carried_input_max_abs_q_v_a':current,
             'native_carried_inputs_and_durations_exactly_equal':exact_inputs,
             'jerk_branch_disagreements':branches,'worst_reference_witnesses':worst}
        results.append(row)
        gate={'passed':len(results)==8 and all(x['passed'] for x in results),'stage':'pre-run finite native state check; no physical runs',
              'limits_q_v_a':LIMITS,'required_pairs':8,'completed_pairs':len(results),'same_input_plans_passed':16,
              'jerk_semantics':'Jerk branch disagreements are reported; state checks do not assert bit-identical branching or a continuous-runtime theorem.',
              'cases':results}
        write('native-pre-run-gate.json',gate)
        print(identity,residual,'exact_inputs',exact_inputs,'jerk_branches',len(branches),'passed',passed,flush=True)
        assert passed,(identity,residual,exact_inputs)
    assert len(results)==8
if __name__=='__main__':main()
