"""The fixed 72 scalar cases at two sampling resolutions; no adaptive tuning."""
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
from bisect import bisect_right
import csv,gzip,json,math,time
import numpy as np
from scipy.linalg import expm
from make_references import state_at

HERE=Path(__file__).resolve().parent
SIGMA=10.
TRACE_FIELDS=['time_s','time_exact','side','labels','q','qv','qa','reference_jerk','reference_snap_piecewise','x','v','a','u','actual_jerk','u_derivative_piecewise','truth','x_minus_q','q_minus_truth','x_minus_truth']

@lru_cache(maxsize=None)
def transition(rate,disturbance,dt):
    # y=(x,v,a,q,qv,qa,j,snap,one), with constant snap on each piece.
    matrix=np.zeros((9,9));matrix[0,1]=1.;matrix[1,2]=1.
    matrix[2,:]=rate*np.array([-800.,-60.,-1.5,800.,60.,1.5,1/96,0.,disturbance])
    for row in [3,4,5,6]:matrix[row,row+1]=1.
    return expm(matrix*dt)

def truth_at(schedule,t,side):
    values=[x['position'] for x in schedule['truth'] if Q(x['time_exact'])<t or (side!='left' and Q(x['time_exact'])==t)]
    return values[-1] if values else schedule['truth'][0]['position']

def output_row(schedule,piece,t,state,side,labels,rate,disturbance):
    q,qv,qa,j,snap=state_at(piece,t)
    x,v,a=map(float,state)
    u=-800*x-60*v-.5*a+800*q+60*qv+1.5*qa+j/96
    actual_j=rate*(u+disturbance-a)
    udot=-800*v-60*a-.5*actual_j+800*qv+60*qa+1.5*j+snap/96
    truth=truth_at(schedule,t,side)
    return dict(zip(TRACE_FIELDS,[float(t),str(t),side,'|'.join(sorted(set(labels))),q,qv,qa,j,snap,x,v,a,u,actual_j,udot,truth,x-q,q-truth,x-truth]))

def run_case(schedule,rate,disturbance,step):
    pieces=schedule['pieces'];starts=[Q(p['start_exact']) for p in pieces]
    horizon=Q(schedule['horizon_exact']);deadline=Q(schedule['deadline_exact'])
    labels={Q(item['time_exact']):list(item['labels']) for item in schedule['common_events']}
    for piece in pieces:
        labels.setdefault(Q(piece['start_exact']),[]).append('reference_boundary')
        labels.setdefault(Q(piece['end_exact']),[]).append('reference_boundary')
    events=sorted(labels)
    assert events[0]==0 and events[-1]==horizon
    state=np.zeros(3);rows=[];jumps=[];energy=0.;continuous_tv=0.;jump_tv=0.
    event_states=[];previous_left=None
    for left,right in zip(events,events[1:]):
        piece=pieces[bisect_right(starts,left)-1]
        assert Q(piece['start_exact'])<=left<right<=Q(piece['end_exact'])
        first=output_row(schedule,piece,left,state,'right',labels[left],rate,disturbance)
        if previous_left is None:
            initial=dict(first);initial['side']='left';rows.append(initial)
        else:
            dq=[first[k]-previous_left[k] for k in ['q','qv','qa','reference_jerk']]
            formula=800*dq[0]+60*dq[1]+1.5*dq[2]+dq[3]/96
            du=first['u']-previous_left['u'];dj=first['actual_jerk']-previous_left['actual_jerk']
            jumps.append({'time_s':float(left),'time_exact':str(left),'labels':first['labels'],'delta_q':dq[0],'delta_qv':dq[1],'delta_qa':dq[2],'delta_reference_jerk':dq[3],
                          'delta_u':du,'delta_actual_jerk':dj,'formula_delta_u':formula,'formula_residual_u':du-formula,'formula_residual_actual_jerk':dj-rate*du,
                          'actual_state_jump_max':max(abs(first[k]-previous_left[k]) for k in ['x','v','a'])})
            jump_tv+=abs(du)
        rows.append(first);event_states.append({'time_exact':str(left),'x':float(state[0]),'v':float(state[1]),'a':float(state[2])})
        first_grid=(left//step)+1
        last_grid=(right- Q(1,10**30))//step
        # The strict comparison also handles phase intervals much smaller than a sample step.
        nodes=[k*step for k in range(int(first_grid),int(last_grid)+1) if left<k*step<right]+[right]
        prev_t=left;prev=first
        for t in nodes:
            dt=float(t-prev_t)
            ref=state_at(piece,prev_t)
            augmented=np.array([*state,*ref,1.],dtype=float)
            state=(transition(float(rate),float(disturbance),dt)@augmented)[:3]
            side='left' if t==right else 'interior'
            row=output_row(schedule,piece,t,state,side,labels.get(t,[]),rate,disturbance)
            energy+=dt*(prev['actual_jerk']**2+row['actual_jerk']**2)/2
            continuous_tv+=dt*(abs(prev['u_derivative_piecewise'])+abs(row['u_derivative_piecewise']))/2
            rows.append(row);prev_t=t;prev=row
        previous_left=rows[-1]
    final=dict(rows[-1]);final['side']='right';final['truth']=truth_at(schedule,horizon,'right')
    final['q_minus_truth']=final['q']-final['truth'];final['x_minus_truth']=final['x']-final['truth'];rows.append(final)
    event_states.append({'time_exact':str(horizon),'x':float(state[0]),'v':float(state[1]),'a':float(state[2])})
    endpoint=next(row for row in rows if Q(row['time_exact'])==deadline and row['side']=='right')
    endpoint_tests=[abs(endpoint['x_minus_truth'])<=.0002,abs(endpoint['v'])<=.001,abs(endpoint['a'])<=.02]
    final_goal=schedule['truth'][-1]['position']
    within=[abs(row['x']-final_goal)<=.0002 and abs(row['v'])<=.001 and abs(row['a'])<=.02 for row in rows]
    last_bad=max((i for i,good in enumerate(within) if not good),default=-1)
    settling=None if last_bad==len(rows)-1 else rows[last_bad+1]['time_s']
    # A boundary has two one-sided rows, so the earlier side cannot hide a later exit.
    hold_peak=max(abs(row['x']) for row in rows)
    internal_peak=max(abs(row['x_minus_q']) for row in rows)
    counts={key:sum(x['outcome']==key for x in schedule['admissions']) for key in ['accepted','jerk_rejected','stale_discard','coalesced_by_larger_sequence']}
    summary={'method':schedule['method'],'case':schedule['case'],'rate':rate,'disturbance':disturbance,'sample_step_s':float(step),'sample_count':len(rows),
             'deadline_s':float(deadline),'horizon_s':float(horizon),'endpoint_error_m':endpoint['x_minus_truth'],'endpoint_v_m_s':endpoint['v'],'endpoint_a_m_s2':endpoint['a'],
             'endpoint_position_pass':endpoint_tests[0],'endpoint_velocity_pass':endpoint_tests[1],'endpoint_acceleration_pass':endpoint_tests[2],'endpoint_pass':all(endpoint_tests),
             'hold_peak_m':hold_peak,'hold_band_pass':hold_peak<=.0002 if schedule['case']=='hold_jitter' else '',
             'internal_error_peak_m':internal_peak,'internal_tube_sample_pass':internal_peak<=.0002,'true_error_peak_m':max(abs(x['x_minus_truth']) for x in rows),
             'shaping_error_peak_m':max(abs(x['q_minus_truth']) for x in rows),'settling_through_horizon_s':settling,
             'actual_jerk_peak_m_s3':max(abs(x['actual_jerk']) for x in rows),'actual_jerk_energy_m2_s5':energy,'actual_jerk_rms_m_s3':math.sqrt(energy/float(horizon)),
             'command_peak_m_s2':max(abs(x['u']) for x in rows),'command_continuous_TV_m_s2':continuous_tv,'command_jump_TV_m_s2':jump_tv,'command_total_variation_m_s2':continuous_tv+jump_tv,
             'largest_command_jump_m_s2':max((abs(x['delta_u']) for x in jumps),default=0.),'largest_actual_jerk_jump_m_s3':max((abs(x['delta_actual_jerk']) for x in jumps),default=0.),
             'reference_velocity_peak_m_s':max(abs(x['qv']) for x in rows),'reference_acceleration_peak_m_s2':max(abs(x['qa']) for x in rows),'reference_jerk_piecewise_peak_m_s3':max(abs(x['reference_jerk']) for x in rows),
             'reference_position_jump_peak_m':max((abs(x['delta_q']) for x in jumps),default=0.),'reference_velocity_jump_peak_m_s':max((abs(x['delta_qv']) for x in jumps),default=0.),'reference_acceleration_jump_peak_m_s2':max((abs(x['delta_qa']) for x in jumps),default=0.),
             'actual_state_jump_max':max((x['actual_state_jump_max'] for x in jumps),default=0.),'command_jump_formula_max_residual':max((abs(x['formula_residual_u']) for x in jumps),default=0.),
             'actual_jerk_jump_formula_max_residual':max((abs(x['formula_residual_actual_jerk']) for x in jumps),default=0.),
             'maximum_packet_age_s':max(float(Q(x['commit_s'])-Q(x['observed_s'])) for x in schedule['admissions']),
             'final_accepted_goal_deviation_m':schedule['final_accepted_goal']-final_goal,**{key+'_count':value for key,value in counts.items()}}
    summary['required_task_sample_pass']=summary['endpoint_pass'] and (summary['hold_band_pass'] is not False)
    stem=f"{schedule['case']}__{schedule['method']}__r{rate}__w{int(round(disturbance*100)):02d}__dt{int(step*1000000)}us"
    traces=HERE/'traces';traces.mkdir(exist_ok=True)
    # gzip timestamp fixed to make output reproducible.
    with (traces/(stem+'.csv.gz')).open('wb') as file:
        with gzip.GzipFile(filename='',mode='wb',fileobj=file,mtime=0) as compressed:
            import io
            with io.TextIOWrapper(compressed,newline='') as text:
                writer=csv.DictWriter(text,fieldnames=TRACE_FIELDS);writer.writeheader();writer.writerows(rows)
    with (traces/(stem+'__events.csv')).open('w',newline='') as file:
        writer=csv.DictWriter(file,fieldnames=list(jumps[0]) if jumps else ['time_s']);writer.writeheader();writer.writerows(jumps)
    return summary,{'case_id':stem,'states':event_states}

def main():
    assert json.loads((HERE/'ruckig-primary-validation.json').read_text())['passed']
    schedules=json.loads((HERE/'reference-schedules.json').read_text())['schedules']
    assert len(schedules)==12
    summaries=[];states=[];started=time.time()
    for step in [Q(1,1000),Q(1,2000)]:
        count=0
        for schedule in schedules:
            for rate in [80,100,120]:
                for disturbance in [0.,.01]:
                    summary,event_state=run_case(schedule,rate,disturbance,step)
                    summaries.append(summary);states.append(event_state);count+=1
            print(f"{float(step):g} s {schedule['case']} {schedule['method']}: {count}/72",flush=True)
        assert count==72
    with (HERE/'metrics.csv').open('w',newline='') as file:
        writer=csv.DictWriter(file,fieldnames=list(summaries[0]));writer.writeheader();writer.writerows(summaries)
    (HERE/'metrics.json').write_text(json.dumps({'status':'builder floating-point numerical evidence; independent review pending','quadrature':'composite trapezoidal energy and integral |u derivative|, with analytic one-sided command jumps added','rows':summaries},indent=2)+'\n')
    (HERE/'event-states.json').write_text(json.dumps(states,indent=2)+'\n')
    print(json.dumps({'parameter_cases':72,'resolutions':2,'elapsed_s':time.time()-started,'transition_cache':str(transition.cache_info())},indent=2))

if __name__=='__main__':main()
