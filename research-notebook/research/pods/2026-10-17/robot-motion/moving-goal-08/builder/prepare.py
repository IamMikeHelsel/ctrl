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

def schedule(case, method):
    events=[]; value=Q(0); outcomes=[]; seen=set()
    for packet in case['packets']:
        seq=packet['sequence']; assert seq not in seen; seen.add(seq)
        issue,ready=map(Q,[packet['observed_s'],packet['ready_s']]); assert ready>=issue
        c=-(-ready//Q(1,50))*Q(1,50); tau=c+Q(case['buffer_s'])
        delta=Q(packet['target_m'])-value
        candidate=events+[(tau,delta)]
        guard=remaining_check(candidate,Q(1,5),Q(15,2),c) if method=='fir' else None
        passed=guard is None or guard['passed']
        row={**packet,'admission_s':str(c),'commit_s':str(tau),'execution_s':str(tau),
             'age_at_commit_s':str(tau-issue),'delta_m':str(delta),
             'outcome':'accepted' if passed else 'jerk_rejected',
             'buffer_s':case['buffer_s'],'deadline_s':case['deadline_s']}
        if guard is not None:
            row.update({'candidate_future_jerk_peak':str(guard['peak_abs']),
                        'candidate_peak_time':str(guard['peak_time']),
                        'checked_knots':[[str(t),str(j)] for t,j in guard['knots']]})
        outcomes.append(row)
        if passed: events=candidate; value=Q(packet['target_m'])
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
    shared={Q(x) for x in ['0','1/5','11/50','7/25','1/2','51/100','13/25','3/5','31/50','17/25','4/5','1','17/10','19/10','5/2']}
    for case in spec['cases']:
        for method in spec['methods']:
            events,value,outcomes=schedule(case,method); end=Q(case['end_s']); key=case['id']+'__'+method
            if method=='fir':pieces=fir(events,Q(1,5),end)
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
                 'execution_clock_records':([{'scheduled_exact':r['execution_s'],'actual_exact':r['execution_s'],'convention':'rational FIR'} for r in outcomes]
                     if method=='fir' else [{'scheduled_exact':r['commit_rational'],'actual_exact':r['native_commit_exact'],'convention':'exact binary native execution origin'} for r in exports[key]])}
            schedules.append(row)
            transcripts.append({'case':case['id'],'method':method,'outcomes':outcomes,'events':[[str(t),str(d)] for t,d in events],'final_accepted_goal':str(value)})
    for method in spec['methods']:
        a=next(s for s in schedules if s['case']=='return_generous' and s['method']==method)
        b=next(s for s in schedules if s['case']=='return_predelivery' and s['method']==method)
        assert a['pieces']==b['pieces'] and a['common_events']==b['common_events'] and a['truth']==b['truth']
    write('reference-schedules.json',{'status':'frozen native06 execution convention; new causal authoritative inputs; no plant run','schedules':schedules})
    write('ruckig-primary-exports.json',exports)
    write('ruckig-primary-validation.json',{'passed':True,'status':'builder checks only','cases':checks})
    write('admission-transcripts.json',{'cases':transcripts})
    write('reference-extrema.json',bounds)
    print(json.dumps({'schedules':len(schedules),'native_plans':sum(map(len,exports.values())),'A_B_reference_identity':True,'FIR_outcomes':[{k:r[k] for k in ['case','outcomes']} for r in transcripts if r['method']=='fir']},indent=2))

if __name__=='__main__':main()
