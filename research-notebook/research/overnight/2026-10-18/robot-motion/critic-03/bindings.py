from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
import csv,gzip,hashlib,json,subprocess,shutil,bisect

HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
B=HERE.parent/'builder-03'
OLD=WORK/'research/pods/2026-10-17/robot-motion/moving-goal-08/builder'
PINNED=WORK/'research/pods/2026-10-17/robot-motion/latency-noise-05/builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads(((B.parent if n.startswith('native-plans/') else B)/n).read_text())
def jet(events,h,t,k):
    return sum((d*(-1)**i*comb(4,i)*max(t-tau-i*h,F(0))**(4-k)/factorial(4-k)/h**4
        for tau,d in events for i in range(5)),F(0))
def bounds(events,c):
    h=F(1,5);knots=sorted({c}|{t+i*h for t,d in events for i in range(5) if t+i*h>=c})
    ap=knots[:]
    for l,r in zip(knots,knots[1:]):
        jl,jr=jet(events,h,l,3),jet(events,h,r,3)
        if jl!=jr:
            z=(l*jr-r*jl)/(jr-jl)
            if l<z<r:ap.append(z)
    return max(abs(jet(events,h,t,2)) for t in ap),max(abs(jet(events,h,t,3)) for t in knots)
spec=read('inputs.json');ss=read('reference-schedules.json')['schedules'];tr=read('admission-transcripts.json')
assert spec['methods']==['fir_checked','native_fast','native_matched'] and spec['rates']==[80,100,120] and spec['disturbances']==['0','1/100'] and spec['output_steps']==['1/1000','1/2000']
assert spec['candidate_execution_times']==['13/25','31/50'] and spec['deadlines']=={'return_generous':'17/10','return_tight':'13/10'}
lookup={(s['case'],s['method']):s for s in ss};trans={(s['case'],s['method']):s for s in tr};outcomes=[];pieces_checked=0
first={'sequence':1,'observed_s':'1/5','ready_s':'11/50','target_m':'1/50','completion_deadline_s':None}
for s in ss:
 case=s['case'];method=s['method'];D=F(s['deadline_exact']);old=[(F(11,50),F(1,50))];events=[];value=F(0)
 assert s['task_spec']['packets'][0]==first and s['admissions'][0]==ss[0]['admissions'][0]
 assert s['truth']==[{'time_exact':'0','position':0.},{'time_exact':'1/5','position':.02},{'time_exact':'1/2','position':0.}]
 assert len(s['admissions'])==2 and s['admissions']==trans[case,method]['admissions']
 assert s['task_spec']['packets'][1]=={'sequence':2,'observed_s':'1/2','ready_s':'13/25','target_m':'0','completion_deadline_s':str(D)}
 if method=='fir_checked':
  for packet,a in zip(s['task_spec']['packets'],s['admissions']):
   assert all(a[k]==v for k,v in packet.items());c=F(packet['ready_s']);delta=F(packet['target_m'])-value;deadline=None if packet['completion_deadline_s'] is None else F(packet['completion_deadline_s'])
   assert a['decision_inputs']=={'available_packet':packet,'retained_events':[[str(t),str(d)] for t,d in events],'current_s':str(c),'target_increment_m':str(delta)}
   candidates=[c] if deadline is None else [F(13,25),F(31,50)];selected=None
   for candidate,trial in zip(candidates,a['candidate_trials']):
    A,J=bounds(events+[(candidate,delta)],c);dok=deadline is None or all(t+F(4,5)<=deadline for t,d in events+[(candidate,delta)])
    accept=candidate>=c and dok and A<=F(1,2) and J<=F(15,2)
    assert F(trial['candidate_s'])==candidate and trial['passed']==accept and trial['full_history_tail_deadline_pass']==dok
    assert F(trial['acceleration_check']['peak_abs'])==A and trial['acceleration_check']['passed']==(A<=F(1,2))
    assert F(trial['jerk_peak'])==J and trial['jerk_pass']==(J<=F(15,2))
    outcomes.append({'case':case,'sequence':packet['sequence'],'candidate':str(candidate),'A':str(A),'J':str(J),'deadline_pass':dok,'accepted':accept})
    if accept:selected=candidate;break
   assert (a['outcome']=='accepted')==(selected is not None) and a['actual_selected_execution_s']==(str(selected) if selected is not None else None)
   if selected is not None:events.append((selected,delta));value=F(packet['target_m'])
  assert trans[case,method]['FIR_events']==[[str(t),str(d)] for t,d in events]
  assert events==(old+[(F(31,50),F(-1,50))] if case=='return_generous' else old)
 else:
  events=old;a=s['admissions'][1];assert a['outcome']=='accepted' and a['admission_s']==a['actual_selected_execution_s']=='13/25'
 assert s['revision_accepted']==(method!='fir_checked' or case=='return_generous')
 assert s['reference_deadline_feasible']==(s['revision_accepted'] and F(s['planned_reference_arrival_exact'])<=D)
 for p in s['pieces']:
  if p['origin']!='exact_four_box':continue
  l,r=F(p['start_exact']),F(p['end_exact']);mid=(l+r)/2;h=F(1,5)
  ds=[sum((amp*(-1)**k*comb(4,k)*(l-tau-k*h)**(4-d)/factorial(4-d)/h**4 for tau,amp in events for k in range(5) if tau+k*h<mid),F(0)) for d in range(5)]
  assert list(map(F,p['rational_derivatives_at_start']))==ds and [p[k] for k in ['p','v','a','jerk','snap']]==list(map(float,ds));pieces_checked+=1
assert [jet([(F(11,50),F(1,50))],F(1,5),F(13,25),k) for k in range(3)]==[F(77,19200),F(23,480),F(5,16)]
identity=0;prefixes={};fields=['time_exact','side','q','qv','qa','reference_jerk','reference_snap_piecewise','x','v','a','u','actual_jerk','truth','x_minus_q','x_minus_truth']
for r in spec['rates']:
 for w in map(F,spec['disturbances']):
  for step in map(F,spec['output_steps']):
   for method in spec['methods']:
    paths=[B/'traces'/f'{case}__{method}__r{r}__w{int(w*100):02d}__dt{int(step*1000000)}us.csv.gz' for case in ['return_generous','return_tight']]
    if method!='fir_checked':assert sha(paths[0])==sha(paths[1]);identity+=1
    for path in paths:
     with gzip.open(path,'rt') as f:rows=[{k:x[k] for k in fields} for x in csv.DictReader(f) if F(x['time_exact'])<F(13,25) or (F(x['time_exact'])==F(13,25) and x['side']=='left')]
     key=(r,w,step)
     if key in prefixes:assert prefixes[key]==rows
     else:prefixes[key]=rows
fig=read('figure-inputs.json');assert all(sha(B/n)==h for n,h in fig['trace_files'].items());assert sha(B/'comparison-summary.json')==fig['summary_sha256']
for frozen in ['pre-run-freeze.json','reference-freeze.json']:
 assert all(sha(B/n)==h for n,h in read(frozen)['files'].items())
out={'status':'PASS','schedules':len(ss),'exact_FIR_pieces':pieces_checked,'candidate_trials':outcomes,'exact_common_reference':['77/19200','23/480','5/16'],'first_request_identical_no_deadline':True,'revision_truth_preserved_after_rejection':True,'native_pairs_identical_across_deadlines':identity,'all_72_prefixes_identical_by_plant_grid':True,'distinct_prefixes':len(prefixes),'figure_hash_binding_pass':True,'pre_run_and_reference_freezes_unchanged':True,'scope':'Independent finite input and exact reference binding, not a universal physical theorem.'}
(HERE/'bindings-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
