"""Run only the frozen48 moving-goal cases, preserving full physical traces."""
from pathlib import Path
from fractions import Fraction as Q
import csv,gzip,hashlib,json,math,time
from run_comparison import run_case,transition

HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')
def trace_stem(s,rate,w,step):return f"{s['case']}__{s['method']}__r{rate}__w{int(round(w*100)):02d}__dt{int(step*1000000)}us"

def task_metrics(schedule,rate,w,step):
    stem=trace_stem(schedule,rate,w,step)
    with gzip.open(HERE/'traces'/(stem+'.csv.gz'),'rt') as f:rows=list(csv.DictReader(f))
    for row in rows:
        row['t_exact']=Q(row['time_exact'])
        for k in ['time_s','q','qv','qa','x','v','a','u','actual_jerk','u_derivative_piecewise','truth','x_minus_q','q_minus_truth','x_minus_truth']:row[k]=float(row[k])
    def at(t):return next(r for r in rows if r['t_exact']==Q(t) and r['side']=='right')
    case=schedule['task_spec'];issue=Q(case['revision_issue_s']);ready=Q(case['revision_ready_s'])
    scheduled_execution=Q(schedule['admissions'][-1]['execution_s'])
    actual_execution=schedule['execution_clock_records'][-1]['actual_exact']
    execution=Q(actual_execution) if actual_execution is not None else scheduled_execution
    start,change=at(0),at(issue);goal=schedule['truth'][-1]['position'];delta=goal-change['x'];direction=1 if delta>0 else -1 if delta<0 else 0
    D=Q(schedule['deadline_exact']);end=Q(schedule['horizon_exact'])
    after=[r for r in rows if r['t_exact']>=D]
    remain=all(abs(r['x']-goal)<=.0002 and abs(r['v'])<=.001 and abs(r['a'])<=.02 for r in after)
    initial_progress=change['x']-start['x'];initial_pass=initial_progress>=.001
    accepted=all(r['outcome']=='accepted' for r in schedule['admissions'])
    causal=actual_execution is not None and D>=execution and D>=ready
    bounds=schedule['reference_extrema'];reference_ok=bounds['common_numerical_conformity']
    points={str(t):{k:at(t)[k] for k in ['x','v','a','q','qv','qa','x_minus_q','q_minus_truth','x_minus_truth']} for t in sorted({issue,ready,execution,scheduled_execution,D,end,Q(3,5),Q(4,5),Q(1)})}
    for p in points.values():p['signed_reversal_progress_m']=direction*(p['x']-change['x'])
    reverse=next((r['time_s'] for r in rows if r['t_exact']>=issue and direction*r['v']>1e-9),None)
    post_energy=post_ctv=0.
    for a,b in zip(rows,rows[1:]):
        dt=float(b['t_exact']-a['t_exact'])
        if a['t_exact']>=issue and dt>0:
            post_energy+=dt*(a['actual_jerk']**2+b['actual_jerk']**2)/2
            post_ctv+=dt*(abs(a['u_derivative_piecewise'])+abs(b['u_derivative_piecewise']))/2
    with (HERE/'traces'/(stem+'__events.csv')).open() as f:jumps=list(csv.DictReader(f))
    post_jtv=sum(abs(float(r['delta_u'])) for r in jumps if Q(r['time_exact'])>=issue)
    metrics={'initial_progress_m':initial_progress,'initial_response_pass':initial_pass,
             'revision_issue_x_m':change['x'],'revision_issue_v_m_s':change['v'],'revision_issue_a_m_s2':change['a'],
             'remaining_signed_distance_at_issue_m':abs(delta),'reversal_direction':direction,
             'revision_ready_s':float(ready),'revision_execution_s':float(execution) if actual_execution is not None else None,'revision_execution_exact':str(execution) if actual_execution is not None else None,
             'revision_scheduled_execution_exact':str(scheduled_execution),
             'first_velocity_toward_revised_goal_s':reverse,
             'deadline_and_remain_sample_pass':remain,'causal_deadline_service_pass':causal,
             'all_authoritative_requests_admitted':accepted,'reference_limits_numerical_pass':reference_ok,
             'reference_peak_velocity_critical_m_s':bounds['peak_V_A_J'][0],
             'reference_peak_acceleration_critical_m_s2':bounds['peak_V_A_J'][1],
             'reference_peak_jerk_critical_m_s3':bounds['peak_V_A_J'][2],
             'post_revision_actual_jerk_squared_integral_m2_s5':post_energy,
             'post_revision_command_continuous_TV_m_s2':post_ctv,'post_revision_command_jump_TV_m_s2':post_jtv,
             'overall_valid_task_numerical_pass':initial_pass and remain and causal and accepted and reference_ok}
    return metrics,{'case_id':stem,'states':points,'reference_extrema':bounds,'method_relative_progress_warning':'Different actual revision positions imply different remaining distances.','trace_sha256':sha(HERE/'traces'/(stem+'.csv.gz'))}

def main():
    assert json.loads((HERE/'native-pre-run-gate.json').read_text())['passed']
    frozen=json.loads((HERE/'pre-run-implementation-manifest.json').read_text())
    for name,h in frozen['files'].items():assert sha(HERE/name)==h,name
    spec=json.loads((HERE/'packets.json').read_text());schedules=json.loads((HERE/'reference-schedules.json').read_text())['schedules'];assert len(schedules)==8
    summaries=[];states=[];details=[];started=time.time()
    for step in map(Q,spec['resolutions_s']):
        count=0
        for schedule in schedules:
            for rate in spec['rates_per_s']:
                for wq in spec['disturbances_m_s2']:
                    w=float(Q(wq));summary,events=run_case(schedule,rate,w,step)
                    extra,detail=task_metrics(schedule,rate,w,step);summary.update(extra)
                    summaries.append(summary);states.append(events);details.append(detail);count+=1
            print(float(step),schedule['case'],schedule['method'],str(count)+'/48',flush=True)
        assert count==48
    identity=[]
    for method in ['ruckig','ruckig_min_08','fir']:
        for rate in spec['rates_per_s']:
            for wq in spec['disturbances_m_s2']:
                for step in map(Q,spec['resolutions_s']):
                    paths=[HERE/'traces'/(f'{name}__{method}__r{rate}__w{int(Q(wq)*100):02d}__dt{int(step*1000000)}us.csv.gz') for name in ['return_generous','return_tight']]
                    hashes=list(map(sha,paths));assert hashes[0]==hashes[1],paths
                    identity.append({'method':method,'rate':rate,'disturbance':wq,'step':str(step),'trace_sha256':hashes[0],'identical':True})
    with (HERE/'metrics.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(summaries[0]));writer.writeheader();writer.writerows(summaries)
    write('metrics.json',{'status':'Builder numerical results; independent review pending.','rows':summaries})
    write('event-states.json',states);write('task-state-diagnostics.json',details);write('A-B-physical-identity.json',identity)
    write('execution-summary.json',{'parameter_cases':48,'resolutions':2,'traces':96,'elapsed_s':time.time()-started,'transition_cache':str(transition.cache_info()),'A_B_trace_pairs_identical':len(identity)})
    print(json.dumps({'completed':len(summaries),'elapsed_s':time.time()-started},indent=2))

if __name__=='__main__':main()
