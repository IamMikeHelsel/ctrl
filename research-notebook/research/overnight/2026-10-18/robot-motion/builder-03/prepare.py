"""Bounded moving-goal schedules. No physical integration in this stage."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import json, hashlib
import numpy as np
from make_references import fir, ruckig, state_at
from knot_check import remaining_check

HERE=Path(__file__).resolve().parent
def write(n,x): (HERE/n).write_text(json.dumps(x,indent=2)+'\n')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def acceleration(events,h,t):
    return sum((d/(2*h**4)*sum(Q(k)*max(t-(tau+i*h),Q(0))**2 for i,k in enumerate([1,-4,6,-4,1])) for tau,d in events),Q(0))
def accel_check(events,h,A,c):
    from knot_check import reference_jerk
    points=[c]+[tau+i*h for tau,_ in events for i in range(5) if c<=tau+i*h]
    base=list(points)
    for L in base:
        for R in base:
            jL,jR=reference_jerk(events,h,L),reference_jerk(events,h,R)
            if L<R and jL!=jR:
                z=(L*jR-R*jL)/(jR-jL)
                if c<=z:points.append(z)
    values=[(t,acceleration(events,h,t)) for t in points]
    t,v=max(values,key=lambda p:abs(p[1]))
    return {'passed':h>0 and A>=0 and abs(v)<=A,'peak_abs':str(abs(v)),'peak_time':str(t),
            'checked_points':[[str(t),str(a)] for t,a in values]}
def schedule(case, method):
    events=[];value=Q(0);outcomes=[];seen=set()
    for packet in case['packets']:
        seq=packet['sequence'];assert seq not in seen;seen.add(seq)
        issue,ready=map(Q,[packet['observed_s'],packet['ready_s']]);assert ready>=issue
        c=-(-ready//Q(1,50))*Q(1,50);delta=Q(packet['target_m'])-value
        D=Q(packet['completion_deadline_s']) if packet['completion_deadline_s'] is not None else None
        candidates=[c] if method!='fir_checked' or D is None else [Q(13,25),Q(31,50)]
        trials=[];selected=None
        for tau in candidates:
            candidate=events+[(tau,delta)]
            jg=remaining_check(candidate,Q(1,5),Q(15,2),c) if method.startswith('fir') else None
            ag=accel_check(candidate,Q(1,5),Q(1,2),c) if method=='fir_checked' else None
            deadline_ok=(D is None or (tau+Q(4,5)<=D and all(t+Q(4,5)<=D for t,_ in events))) if method=='fir_checked' else True
            causal=c<=tau
            passed=causal and deadline_ok and (jg is None or jg['passed']) and (ag is None or ag['passed'])
            trials.append({'candidate_s':str(tau),'causal':causal,'deadline_seen':None if D is None else str(D),
                'full_history_tail_deadline_pass':deadline_ok,'jerk_pass':None if jg is None else jg['passed'],
                'jerk_peak':None if jg is None else str(jg['peak_abs']), 'acceleration_check':ag,'passed':passed})
            if passed:selected=tau;break
        passed=selected is not None;tau=selected if passed else c
        row={**packet,'admission_s':str(c),'commit_s':str(tau),'execution_s':str(tau),
             'requested_execution_s':str(c),'actual_selected_execution_s':str(selected) if passed else None,
             'age_at_commit_s':str(tau-issue),'delta_m':str(delta),
             'outcome':'accepted' if passed else ('candidate_set_rejected' if method=='fir_checked' else 'jerk_rejected'),
             'buffer_s':'0','candidate_trials':trials,
             'decision_inputs':{'available_packet':packet,'retained_events':[[str(t),str(d)] for t,d in events],
                'current_s':str(c),'target_increment_m':str(delta)}}
        outcomes.append(row)
        if passed:events=events+[(tau,delta)];value=Q(packet['target_m'])
    return events,value,outcomes

def reference_extrema(pieces):
    peaks=[0.,0.,0.]; witnesses=[None,None,None]; exact_a=Q(0); exact_j=Q(0)
    exact_fir=all('rational_derivatives_at_start' in p for p in pieces)
    for p in pieces:
        width=float(Q(p['end_exact'])-Q(p['start_exact']))
        a,j,s=p['a'],p['jerk'],p['snap']
        nodes={0.,width}
        coefficients=[s/2,j,a]
        while coefficients and coefficients[0]==0: coefficients.pop(0)
        if len(coefficients)>1:
            for z in np.roots(coefficients):
                if abs(z.imag)<=1e-12 and 0<float(z.real)<width:nodes.add(float(z.real))
        if s and 0<-j/s<width:nodes.add(-j/s)
        for z in sorted(nodes):
            vals=[p['v']+a*z+j*z*z/2+s*z**3/6,a+j*z+s*z*z/2,j+s*z]
            for k,val in enumerate(vals):
                if abs(val)>peaks[k]:peaks[k]=abs(val);witnesses[k]={'piece_start':p['start_exact'],'offset_s':z,'signed_value':val}
        if exact_fir:
            ds=list(map(Q,p['rational_derivatives_at_start'])); w=Q(p['end_exact'])-Q(p['start_exact'])
            ns={Q(0),w}
            if ds[4] and 0<-ds[3]/ds[4]<w:ns.add(-ds[3]/ds[4])
            exact_a=max(exact_a,*(abs(ds[2]+ds[3]*z+ds[4]*z*z/2) for z in ns))
            exact_j=max(exact_j,abs(ds[3]),abs(ds[3]+ds[4]*w))
    limits=[.1,.5,7.5]
    return {'peak_V_A_J':peaks,'witnesses':witnesses,'nominal_limits':limits,
            'signed_nominal_excess':[p-l for p,l in zip(peaks,limits)],
            'common_absolute_numerical_allowance':1e-10,
            'common_numerical_conformity':all(p<=l+1e-10 for p,l in zip(peaks,limits)),
            'exact_FIR_acceleration_peak':str(exact_a) if exact_fir else None,
            'exact_FIR_jerk_peak':str(exact_j) if exact_fir else None,
            'scope':'Reference extrema only. Native values are floating evaluations of exact exported polynomial data; no exact limit theorem.'}

def main():
    frozen=json.loads((HERE/'pre-run-input-manifest.json').read_text())
    for n,h in frozen['files'].items():assert sha(HERE/n)==h,n
    spec=json.loads((HERE/'packets.json').read_text()); schedules=[];exports={};checks={};transcripts=[];bounds={}
    shared={Q(x) for x in ['0','1/5','11/50','1/2','13/25','3/5','31/50','4/5','1','51/50','33/25','71/50','13/10','17/10','5/2']}
    for case in spec['cases']:
        for method in spec['methods']:
            events,value,outcomes=schedule(case,method); end=Q(case['end_s']); key=case['id']+'__'+method
            if method.startswith('fir'):pieces=fir(events,Q(1,5),end)
            else:pieces,exports[key],checks[key]=ruckig(events,end,.8 if method=='ruckig_min_08' else 0.,key)
            assert Q(pieces[0]['start_exact'])==0 and Q(pieces[-1]['end_exact'])==end
            for a,b in zip(pieces,pieces[1:]):assert Q(a['end_exact'])==Q(b['start_exact']),(key,a,b)
            common={t:['shared_scoring_probe'] for t in shared}
            def add(t,label): common.setdefault(Q(t),[]).append(label)
            for item in case['truth']:add(item['time_s'],'truth_change')
            for item in outcomes:
                add(item['observed_s'],'authoritative_issue');add(item['ready_s'],'ready')
                add(item['admission_s'],'admission_'+item['outcome']);add(item['execution_s'],'execution_'+item['outcome'])
            tail=max((t for t,d in events),default=Q(0))+Q(4,5)
            if tail<=end:add(tail,'fir_or_input_final_tail')
            bounds[key]=reference_extrema(pieces)
            row={'method':method,'case':case['id'],'hold_required':False,
                 'horizon':float(end),'horizon_exact':str(end),
                 'deadline':float(Q(case['deadline_s'])),'deadline_exact':case['deadline_s'],
                 'truth':[{'time':float(Q(x['time_s'])),'time_exact':x['time_s'],'position':float(Q(x['position_m']))} for x in case['truth']],
                 'common_events':[{'time':float(t),'time_exact':str(t),'labels':labels} for t,labels in sorted(common.items())],
                 'admissions':outcomes,'final_accepted_goal':float(value),'pieces':pieces,
                 'reference_extrema':bounds[key], 'task_spec':case,
                 'execution_clock_records':([{'scheduled_exact':r['execution_s'],'actual_exact':r['actual_selected_execution_s'],'convention':'rational FIR'} for r in outcomes]
                     if method.startswith('fir') else [{'scheduled_exact':r['commit_rational'],'actual_exact':r['native_commit_exact'],'convention':'exact binary native execution origin'} for r in exports[key]])}
            schedules.append(row)
            transcripts.append({'case':case['id'],'method':method,'outcomes':outcomes,'events':[[str(t),str(d)] for t,d in events],'final_accepted_goal':str(value)})
    for method in ['ruckig','ruckig_min_08','fir']:
        a=next(s for s in schedules if s['case']=='return_generous' and s['method']==method)
        b=next(s for s in schedules if s['case']=='return_tight' and s['method']==method)
        assert a['pieces']==b['pieces'] and a['common_events']==b['common_events'] and a['truth']==b['truth']
    first=[s['admissions'][0]['decision_inputs'] for s in schedules]
    assert all(x['available_packet']['completion_deadline_s'] is None for x in first)
    for method in spec['methods']:
        ss=[s for s in schedules if s['method']==method]
        assert ss[0]['admissions'][0]==ss[1]['admissions'][0]
    write('reference-schedules.json',{'status':'frozen native06 execution convention; new causal authoritative inputs; no plant run','schedules':schedules})
    write('ruckig-primary-exports.json',exports)
    write('ruckig-primary-validation.json',{'passed':True,'status':'builder checks only','cases':checks})
    write('admission-transcripts.json',{'cases':transcripts})
    write('reference-extrema.json',bounds)
    print(json.dumps({'schedules':len(schedules),'native_plans':sum(map(len,exports.values())),'unchanged_method_deadline_reference_identity':True,'FIR_outcomes':[{k:r[k] for k in ['case','outcomes']} for r in transcripts if r['method'].startswith('fir')]},indent=2))

if __name__=='__main__':main()
