#!/usr/bin/env python3
"""Independent 80-digit physical replay: polynomial particular solution plus
3x3 homogeneous matrix exponential. No builder code or simulated states imported.
"""
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_left,bisect_right
from functools import lru_cache
from math import factorial
import csv,gzip,hashlib,json,time,sys
import mpmath as mp
mp.mp.dps=80
HERE=Path(__file__).resolve().parent;BUILDER=HERE.parent/'builder-02/runtime-replay-02'
FIELDS=['q','qv','qa','reference_jerk','reference_snap_piecewise','x','v','a','u','actual_jerk','u_derivative_piecewise','truth','x_minus_q','q_minus_truth','x_minus_truth']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def m(q):
    q=Q(q);return mp.mpf(q.numerator)/q.denominator

def ev(cs,t):
    y=mp.mpf(0)
    for c in reversed(cs):y=y*t+c
    return y

@lru_cache(maxsize=None)
def transition(rate,dt):
    if dt==0:return mp.eye(3)
    a=mp.matrix([[0,1,0],[0,0,1],[-800*rate,-60*rate,-mp.mpf(3)*rate/2]])
    return mp.expm(a*m(dt),method='pade')
def mv(M,v):return [sum(M[i,j]*v[j] for j in range(3)) for i in range(3)]

def particular(piece,rate,disturbance):
    # q coefficients encode each frozen binary float exactly before high-precision work.
    q=[Q(piece[k])/factorial(i) for i,k in enumerate(['p','v','a','jerk','snap'])]
    ds=[[q[i]*Q(factorial(i),factorial(i-k)) for i in range(k,5)] for k in range(5)]
    force=[]
    for i in range(5):
        val=800*ds[0][i]+(60*ds[1][i] if i<4 else 0)+(Q(3,2)*ds[2][i] if i<3 else 0)+(ds[3][i]/96 if i<2 else 0)
        force.append(rate*(val+(disturbance if i==0 else 0)))
    p=[Q(0)]*8
    for i in range(4,-1,-1):
        p[i]=(force[i]-Q(3*rate,2)*(i+2)*(i+1)*p[i+2]-60*rate*(i+1)*p[i+1]-(i+3)*(i+2)*(i+1)*p[i+3])/(800*rate)
    for i in range(5):assert 800*rate*p[i]+60*rate*(i+1)*p[i+1]+Q(3*rate,2)*(i+2)*(i+1)*p[i+2]+(i+3)*(i+2)*(i+1)*p[i+3]==force[i]
    pd=[[m(p[i]*Q(factorial(i),factorial(i-k))) for i in range(k,5)] for k in range(3)]
    return [[m(x) for x in d] for d in ds],pd

def dump(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
manifest=json.loads((BUILDER/'data-sha256.json').read_text())
assert len(sys.argv)==2, 'Pass the independently supplied frozen manifest hash'
assert sha(BUILDER/'data-sha256.json')==sys.argv[1]
assert len(manifest['files']) > 192
assert all(sha(BUILDER/n)==v for n,v in manifest['files'].items())
schedules=json.loads((BUILDER/'reference-schedules.json').read_text())['schedules']
metrics=json.loads((BUILDER/'metrics.json').read_text())['rows']
lookup={(s['case'],s['method']):s for s in schedules}
diagnostics={r['case_id']:r for r in json.loads((BUILDER/'task-state-diagnostics.json').read_text())}
assert len(metrics)==96 and len(schedules)==8
# Critical points of each frozen reference polynomial, computed independently.
def reference_extrema(pieces):
    peaks=[mp.mpf(0)]*3
    for p in pieces:
        dur=m(Q(p['end_exact'])-Q(p['start_exact']))
        v,a,j,snap=[m(p[k]) for k in ['v','a','jerk','snap']]
        vc=[mp.mpf(0),dur];ac=[mp.mpf(0),dur]
        if snap:
            disc=j*j-2*snap*a
            if disc>=0:vc.extend([(-j+mp.sqrt(disc))/snap,(-j-mp.sqrt(disc))/snap])
            ac.append(-j/snap)
        elif j:vc.append(-a/j)
        peaks[0]=max([peaks[0]]+[abs(v+a*t+j*t*t/2+snap*t**3/6) for t in vc if 0<=t<=dur])
        peaks[1]=max([peaks[1]]+[abs(a+j*t+snap*t*t/2) for t in ac if 0<=t<=dur])
        peaks[2]=max(peaks[2],abs(j),abs(j+snap*dur))
    return peaks

report={'status':'running','precision_decimal_digits':80,'method':'Exact rational polynomial particular coefficients; mpmath Pade 3x3 homogeneous exponential. All trajectories start from zero; no primary actual state reused.',
        'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'manifest_before':sha(BUILDER/'data-sha256.json'),'case_results':[],'max_row_differences':{k:0. for k in FIELDS},'metric_max_differences':{},'decision_mismatches':[],'event_max_differences':{},'total_rows':0,'total_events':0}
# Hold Ruckig first: this is the surprising result under review.
metrics.sort(key=lambda a:(not (a['case']=='hold_jitter' and a['method']=='ruckig'),a['sample_step_s'],a['case'],a['method'],a['rate'],a['disturbance']))
start=time.monotonic()
for index,primary in enumerate(metrics):
    s=lookup[primary['case'],primary['method']];rate=primary['rate'];w=Q(str(primary['disturbance']));step=Q(str(primary['sample_step_s']))
    stem=f"{s['case']}__{s['method']}__r{rate}__w{int(w*100):02d}__dt{int(step*1000000)}us"
    pieces=s['pieces'];starts=[Q(p['start_exact']) for p in pieces];ends=[Q(p['end_exact']) for p in pieces]
    assert starts[0]==0 and all(a==b for a,b in zip(ends,starts[1:])) and ends[-1]==Q(s['horizon_exact'])
    models=[particular(p,rate,w) for p in pieces]
    horizon=ends[-1];deadline=Q(s['deadline_exact'])
    events={Q(e['time_exact']) for e in s['common_events']}|set(starts)|set(ends)
    expected=[]
    for t in sorted(events|{k*step for k in range(int(horizon//step)+1)}):
        expected.extend([(t,'left'),(t,'right')] if t in events else [(t,'interior')])
    with gzip.open(BUILDER/'traces'/(stem+'.csv.gz'),'rt') as f: saved=list(csv.DictReader(f))
    assert [(Q(r['time_exact']),r['side']) for r in saved]==expected,(stem,'grid mismatch')
    assert len(saved)==primary['sample_count']
    state=[mp.mpf(0)]*3;previous_t=Q(0);piece_index=0
    h=[state[i]-models[0][1][i][0] for i in range(3)]
    peaks={k:mp.mpf(0) for k in FIELDS};maxdiff={k:mp.mpf(0) for k in FIELDS};eventdiff={};digest=hashlib.sha256()
    energy=mp.mpf(0);tv=mp.mpf(0);jtv=mp.mpf(0);peak_jump=mp.mpf(0);peak_jjump=mp.mpf(0)
    refjumps=[mp.mpf(0)]*3;maxstatejump=mp.mpf(0);endpoint=None;previous=None;peak_hold=None;settling=0.;last_good_candidate=0.;last_was_bad=False
    event_rows=[];event_out=[];final_goal=m(Q(s['truth'][-1]['position']))
    spec=s['task_spec'];issue=Q(spec['revision_issue_s']);ready=Q(spec['revision_ready_s'])
    actual_execution=s['execution_clock_records'][-1]['actual_exact'];scheduled_execution=Q(s['admissions'][-1]['execution_s'])
    execution=Q(actual_execution) if actual_execution is not None else scheduled_execution
    at_issue=None;initial_x=None;direction=None;first_toward=None;remain=True
    post_energy=mp.mpf(0);post_ctv=mp.mpf(0);post_jtv=mp.mpf(0);diagdiff={}
    refpeaks=reference_extrema(pieces)
    numerical_limits_pass=all(z<=limit+mp.mpf('1e-10') for z,limit in zip(refpeaks,map(mp.mpf,['.1','.5','7.5'])))

    for row,(t,side) in zip(saved,expected):
        idx=bisect_left(starts,t)-1 if side=='left' and t>0 else bisect_right(starts,t)-1
        idx=min(max(idx,0),len(pieces)-1)
        dt=t-previous_t;assert dt>=0 and t<=ends[piece_index]
        if dt:h=mv(transition(rate,dt),h)
        elapsed=m(t-starts[piece_index]);pd=models[piece_index][1]
        state=[ev(pd[i],elapsed)+h[i] for i in range(3)]
        if idx!=piece_index:
            assert idx==piece_index+1 and t==starts[idx],(stem,piece_index,idx,t)
            piece_index=idx;elapsed=mp.mpf(0);pd=models[idx][1]
            h=[state[i]-pd[i][0] for i in range(3)]
        q,qv,qa,j,snap=[ev(d,elapsed) for d in models[idx][0]]
        x,v,a=state
        u=800*(q-x)+60*(qv-v)+mp.mpf('1.5')*qa-mp.mpf('.5')*a+j/96
        physical_j=rate*(u+m(w)-a)
        ud=-800*v-60*a-physical_j/2+800*qv+60*qa+mp.mpf('1.5')*j+snap/96
        truth=next(m(Q(d['position'])) for d in reversed(s['truth']) if Q(d['time_exact'])<t or (side!='left' and Q(d['time_exact'])==t)) if t!=0 or side!='left' else m(Q(s['truth'][0]['position']))
        vals=dict(zip(FIELDS,[q,qv,qa,j,snap,x,v,a,u,physical_j,ud,truth,x-q,q-truth,x-truth]))
        for k,z in vals.items():
            peaks[k]=max(peaks[k],abs(z));maxdiff[k]=max(maxdiff[k],abs(z-mp.mpf(row[k])))
        if peak_hold is None or abs(x)>abs(mp.mpf(peak_hold['x'])):
            peak_hold={'time_exact':str(t),'side':side,**{k:mp.nstr(vals[k],55) for k in ['q','x','v','a','u','actual_jerk','x_minus_q']}}
        digest.update((str(t)+'|'+side+'|'+','.join(mp.nstr(vals[k],55) for k in FIELDS)+'\n').encode())
        if t==0 and side=='right':initial_x=x
        if t==issue and side=='right':
            at_issue={'x':x,'v':v,'a':a}
            direction=1 if final_goal>x else -1 if final_goal<x else 0
        if t>=deadline:remain=remain and abs(x-final_goal)<=mp.mpf('.0002') and abs(v)<=mp.mpf('.001') and abs(a)<=mp.mpf('.02')
        if t>=issue and direction is not None and first_toward is None and direction*v>mp.mpf('1e-9'):first_toward=float(t)
        if side=='right' and str(t) in diagnostics[stem]['states']:
            for k,z in diagnostics[stem]['states'][str(t)].items():
                expected_val=direction*(x-at_issue['x']) if k=='signed_reversal_progress_m' else vals[k]
                diagdiff[k]=max(diagdiff.get(k,0.),float(abs(expected_val-mp.mpf(z))))
        if previous is not None:
            if dt:
                if previous_t>=issue:
                    post_energy+=m(dt)*(previous['actual_jerk']**2+physical_j**2)/2
                    post_ctv+=m(dt)*(abs(previous['u_derivative_piecewise'])+abs(ud))/2

                energy+=m(dt)*(previous['actual_jerk']**2+physical_j**2)/2
                tv+=m(dt)*(abs(previous['u_derivative_piecewise'])+abs(ud))/2
            elif side=='right' and t not in [Q(0),horizon]:
                du=u-previous['u'];dj=physical_j-previous['actual_jerk'];dq=[vals[k]-previous[k] for k in ['q','qv','qa','reference_jerk']]
                if t>=issue:post_jtv+=abs(du)
                jtv+=abs(du);peak_jump=max(peak_jump,abs(du));peak_jjump=max(peak_jjump,abs(dj))
                for i in range(3):refjumps[i]=max(refjumps[i],abs(dq[i]))
                formula=800*dq[0]+60*dq[1]+mp.mpf('1.5')*dq[2]+dq[3]/96
                jumpstate=max(abs(vals[k]-previous[k]) for k in ['x','v','a']);maxstatejump=max(maxstatejump,jumpstate)
                event_out.append({'time_exact':str(t),'delta_q':dq[0],'delta_qv':dq[1],'delta_qa':dq[2],'delta_reference_jerk':dq[3],'delta_u':du,'delta_actual_jerk':dj,'formula_delta_u':formula,'formula_residual_u':du-formula,'formula_residual_actual_jerk':dj-rate*du,'actual_state_jump_max':jumpstate})
        if t==deadline and side=='right':endpoint={k:vals[k] for k in ['x_minus_truth','v','a']}
        good=abs(x-final_goal)<=mp.mpf('.0002') and abs(v)<=mp.mpf('.001') and abs(a)<=mp.mpf('.02')
        if good and last_was_bad:last_good_candidate=float(t)
        if not good:last_good_candidate=None
        last_was_bad=not good
        if side=='right' and t in events:
            event_rows.append({'time_exact':str(t),**{k:mp.nstr(vals[k],55) for k in ['x','v','a']}})
        previous=vals;previous_t=t
    assert endpoint is not None
    ep=[abs(endpoint[k])<=lim for k,lim in [('x_minus_truth',mp.mpf('.0002')),('v',mp.mpf('.001')),('a',mp.mpf('.02'))]]
    hold=peaks['x']<=mp.mpf('.0002') if s['hold_required'] else ''
    measured={'endpoint_error_m':endpoint['x_minus_truth'],'endpoint_v_m_s':endpoint['v'],'endpoint_a_m_s2':endpoint['a'],
      'endpoint_position_pass':ep[0],'endpoint_velocity_pass':ep[1],'endpoint_acceleration_pass':ep[2],'endpoint_pass':all(ep),
      'hold_peak_m':peaks['x'],'hold_band_pass':hold,'internal_error_peak_m':peaks['x_minus_q'],'internal_tube_sample_pass':peaks['x_minus_q']<=mp.mpf('.0002'),
      'true_error_peak_m':peaks['x_minus_truth'],'shaping_error_peak_m':peaks['q_minus_truth'],'settling_through_horizon_s':last_good_candidate,
      'actual_jerk_peak_m_s3':peaks['actual_jerk'],'actual_jerk_energy_m2_s5':energy,'actual_jerk_rms_m_s3':mp.sqrt(energy/m(horizon)),
      'command_peak_m_s2':peaks['u'],'command_continuous_TV_m_s2':tv,'command_jump_TV_m_s2':jtv,'command_total_variation_m_s2':tv+jtv,
      'largest_command_jump_m_s2':peak_jump,'largest_actual_jerk_jump_m_s3':peak_jjump,'reference_velocity_peak_m_s':peaks['qv'],
      'reference_acceleration_peak_m_s2':peaks['qa'],'reference_jerk_piecewise_peak_m_s3':peaks['reference_jerk'],
      'reference_position_jump_peak_m':refjumps[0],'reference_velocity_jump_peak_m_s':refjumps[1],'reference_acceleration_jump_peak_m_s2':refjumps[2],
      'actual_state_jump_max':maxstatejump,'required_task_sample_pass':all(ep) and hold is not False}
    assert at_issue is not None and initial_x is not None
    initial_progress=at_issue['x']-initial_x
    initial_pass=initial_progress>=mp.mpf('.001')
    accepted=all(o['outcome']=='accepted' for o in s['admissions'])
    causal=actual_execution is not None and deadline>=execution and deadline>=ready
    measured.update({'initial_progress_m':initial_progress,'initial_response_pass':initial_pass,
      'revision_issue_x_m':at_issue['x'],'revision_issue_v_m_s':at_issue['v'],'revision_issue_a_m_s2':at_issue['a'],
      'remaining_signed_distance_at_issue_m':abs(final_goal-at_issue['x']),'reversal_direction':direction,
      'revision_ready_s':float(ready),'revision_execution_s':float(execution) if actual_execution is not None else None,
      'first_velocity_toward_revised_goal_s':first_toward,'deadline_and_remain_sample_pass':remain,
      'causal_deadline_service_pass':causal,'all_authoritative_requests_admitted':accepted,
      'reference_limits_numerical_pass':numerical_limits_pass,
      'reference_peak_velocity_critical_m_s':refpeaks[0],'reference_peak_acceleration_critical_m_s2':refpeaks[1],
      'reference_peak_jerk_critical_m_s3':refpeaks[2],
      'post_revision_actual_jerk_squared_integral_m2_s5':post_energy,
      'post_revision_command_continuous_TV_m_s2':post_ctv,'post_revision_command_jump_TV_m_s2':post_jtv,
      'overall_valid_task_numerical_pass':initial_pass and remain and causal and accepted and numerical_limits_pass})
    assert primary['revision_execution_exact']==(str(execution) if actual_execution is not None else None)
    assert primary['revision_scheduled_execution_exact']==str(scheduled_execution)
    diffs={}
    for k,z in measured.items():
        p=primary[k]
        if isinstance(z,bool) or z is None or z=='':
            if z!=p:report['decision_mismatches'].append({'case':stem,'metric':k,'primary':p,'review':z})
        else:
            d=abs(float(z)-p);diffs[k]=d;report['metric_max_differences'][k]=max(d,report['metric_max_differences'].get(k,0.))
    with (BUILDER/'traces'/(stem+'__events.csv')).open() as f:raw_events=list(csv.DictReader(f))
    assert len(raw_events)==len(event_out)
    for a,b in zip(raw_events,event_out):
        assert a['time_exact']==b['time_exact']
        for k,z in b.items():
            if k=='time_exact':continue
            d=float(abs(z-mp.mpf(a[k])));eventdiff[k]=max(d,eventdiff.get(k,0.));report['event_max_differences'][k]=max(d,report['event_max_differences'].get(k,0.))
    converted={k:(float(z) if isinstance(z,mp.mpf) else z) for k,z in measured.items()}
    result={'case_id':stem,'row_count':len(saved),'event_count':len(event_out),'row_output_sha256_55_digit':digest.hexdigest(),
      'max_row_differences':{k:float(v) for k,v in maxdiff.items()},'task_state_diagnostic_differences':diagdiff,'metric_differences':diffs,'event_max_differences':eventdiff,'metrics':converted,'peak_hold_witness':peak_hold}
    for k,z in maxdiff.items():report['max_row_differences'][k]=max(float(z),report['max_row_differences'][k])
    report['total_rows']+=len(saved);report['total_events']+=len(event_out);report['case_results'].append(result)
    if step==Q(1,2000):
        dump(HERE/(stem+'-event-states.json'),event_rows)
    report['elapsed_seconds']=time.monotonic()-start;report['transition_cache']=str(transition.cache_info())
    dump(HERE/'physical-review.json',report)
    print(index+1,len(metrics),stem,'max x diff',float(maxdiff['x']),'task',converted['required_task_sample_pass'],'seconds',round(report['elapsed_seconds'],1),flush=True)
report['all_artifacts_unchanged']=all(sha(BUILDER/n)==v for n,v in manifest['files'].items()) and sha(BUILDER/'data-sha256.json')==report['manifest_before']
report['status']='complete'
report['passed']=not report['decision_mismatches'] and report['all_artifacts_unchanged'] and max(report['max_row_differences'].values())<1e-7
report['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());dump(HERE/'physical-review.json',report)
print(json.dumps({k:report[k] for k in ['passed','total_rows','total_events','elapsed_seconds','decision_mismatches','max_row_differences']}),flush=True)
