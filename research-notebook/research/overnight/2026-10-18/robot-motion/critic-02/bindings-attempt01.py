from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
import csv,gzip,hashlib,json,subprocess,shutil,bisect

HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
B=HERE.parent/'builder-02/runtime-replay-02'
OLD=WORK/'research/pods/2026-10-17/robot-motion/moving-goal-08/builder'
PINNED=WORK/'research/pods/2026-10-17/robot-motion/latency-noise-05/builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((B/n).read_text())
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
spec=read('packets.json');ss=read('reference-schedules.json')['schedules'];tt=read('admission-transcripts.json')['cases']
lookup={(s['case'],s['method']):s for s in ss};trans={(t['case'],t['method']):t for t in tt}
assert len(ss)==8 and spec['methods']==['ruckig','ruckig_min_08','fir','fir_checked']
assert spec['rates_per_s']==[80,100,120] and spec['disturbances_m_s2']==['0','1/100'] and spec['resolutions_s']==['1/1000','1/2000']
assert spec['revision_candidates_s']==['13/25','31/50']
fir_count=native_count=0;clock_diffs=[];outcomes=[]
for case in spec['cases']:
 assert case['end_s']=='5/2' and case['revision_issue_s']=='1/2'
 assert case['packets'][0]=={'sequence':100,'observed_s':'1/5','ready_s':'11/50','target_m':'1/50','completion_deadline_s':None}
 assert case['packets'][1]['completion_deadline_s']==case['deadline_s']
 for method in spec['methods']:
  key=(case['id'],method);s=lookup[key];tr=trans[key]
  assert s['task_spec']==case and len(s['admissions'])==2 and s['admissions']==tr['outcomes']
  events=[];value=F(0)
  for packet,o in zip(case['packets'],s['admissions']):
   assert all(o[k]==v for k,v in packet.items())
   c=-(-F(packet['ready_s'])//F(1,50))*F(1,50)
   delta=F(packet['target_m'])-value
   assert F(o['admission_s'])==c and F(o['delta_m'])==delta
   assert o['decision_inputs']['retained_events']==[[str(t),str(d)] for t,d in events]
   assert o['decision_inputs']['available_packet']==packet
   D=None if packet['completion_deadline_s'] is None else F(packet['completion_deadline_s'])
   candidates=[c] if method!='fir_checked' or D is None else [F(13,25),F(31,50)]
   selected=None
   for tau,trial in zip(candidates,o['candidate_trials']):
    A,J=bounds(events+[(tau,delta)],c)
    deadline_ok=method!='fir_checked' or D is None or all(t+F(4,5)<=D for t,d in events+[(tau,delta)])
    accept=(c<=tau and deadline_ok and (not method.startswith('fir') or J<=F(15,2)) and (method!='fir_checked' or A<=F(1,2)))
    assert F(trial['candidate_s'])==tau and trial['passed']==accept
    assert trial['full_history_tail_deadline_pass']==deadline_ok
    if method.startswith('fir'):
     assert trial['jerk_pass']==(J<=F(15,2)) and F(trial['jerk_peak'])==J
    if method=='fir_checked':assert trial['acceleration_check']['passed']==(A<=F(1,2)) and F(trial['acceleration_check']['peak_abs'])==A
    if accept:selected=tau;break
   assert (o['outcome']=='accepted')==(selected is not None)
   assert o['actual_selected_execution_s']==(str(selected) if selected is not None else None)
   assert F(o['execution_s'])==(selected if selected is not None else c)
   outcomes.append({'case':case['id'],'method':method,'sequence':packet['sequence'],'outcome':o['outcome'],'selected':str(selected) if selected is not None else None})
   if selected is not None:events.append((selected,delta));value=F(packet['target_m'])
  assert events==[tuple(map(F,x)) for x in tr['events']] and value==F(tr['final_accepted_goal'])
  assert [F(p['end_exact']) for p in s['pieces'][:-1]]==[F(p['start_exact']) for p in s['pieces'][1:]]
  assert F(s['pieces'][0]['start_exact'])==0 and F(s['pieces'][-1]['end_exact'])==F(5,2)
  if method.startswith('fir'):
   for p in s['pieces']:
    l,r=map(F,[p['start_exact'],p['end_exact']]);mid=(l+r)/2;h=F(1,5)
    ds=[sum((amp*(-1)**k*comb(4,k)*(l-tau-k*h)**(4-d)/factorial(4-d)/h**4
       for tau,amp in events for k in range(5) if tau+k*h<mid),F(0)) for d in range(5)]
    assert list(map(F,p['rational_derivatives_at_start']))==ds
    assert [p[k] for k in ['p','v','a','jerk','snap']]==list(map(float,ds));fir_count+=1
  else:
   stem='__'.join(key);records=read('native-plans/'+stem+'-output.json');md=.8 if method=='ruckig_min_08' else 0.
   assert records['minimum_duration']==md and len(records['plans'])==2
   inputlines=(B/'native-plans'/(stem+'-input.txt')).read_text().splitlines();assert int(inputlines[0])==2
   expected=[]
   for i,(o,record,line) in enumerate(zip(s['admissions'],records['plans'],inputlines[1:])):
    tau=float(F(o['execution_s']));target=float(F(o['target_m']));assert list(map(float,line.split()))==[tau,target]
    assert record['native_commit']==tau and record['target']==target and o['outcome']=='accepted'
    origin=F(tau);stop=F(float(F(s['admissions'][i+1]['execution_s']))) if i==0 else F(5,2)
    assert s['execution_clock_records'][i]['actual_exact']==str(origin);clock_diffs.append(str(origin-F(o['execution_s'])))
    plan=record['plan'];assert plan['minimum_duration']==md
    if i==0:
     assert record['current_state']==[0,0,0];expected.append((F(0),origin,[0.,0.,0.,0.,0.],'initial_rest'))
    else:
     prev=records['plans'][i-1];elapsed=tau-prev['native_commit'];assert prev['native_elapsed_to_next_commit_or_horizon']==elapsed
     samples=[q for q in prev['plan']['samples'] if q['t']==elapsed]
     assert samples and all([q[k] for k in ['p','v','a']]==record['current_state'] for q in samples)
    for phase in plan['phases']:
     if phase['duration']<=0:continue
     start=origin+F(phase['start']);end=min(stop,origin+F(phase['end']))
     if start<end:expected.append((start,end,[phase[k] for k in ['p','v','a','jerk']]+[0.],f'plan_{i}_{phase["kind"]}_{phase["index"]}'))
    tail=plan['tail'];start=origin+F(tail['start'])
    if start<stop:expected.append((start,stop,[tail[k] for k in ['p','v','a','jerk']]+[0.],f'plan_{i}_extrapolated_tail'))
    native_count+=1
   actual=[(F(p['start_exact']),F(p['end_exact']),[p[k] for k in ['p','v','a','jerk','snap']],p['origin']) for p in s['pieces']]
   assert actual==expected,stem
   if case['id']=='return_generous':
    for suffix in ['-input.txt','-output.json']:assert (B/'native-plans'/(stem+suffix)).read_bytes()==(OLD/'native-plans'/(stem+suffix)).read_bytes()
for method in spec['methods']:
 a,b=[lookup[(c,method)] for c in ['return_generous','return_tight']]
 assert a['admissions'][0]==b['admissions'][0]
 if method!='fir_checked':assert all(a[k]==b[k] for k in ['pieces','truth','common_events'])
identity=0;prefixes=0
for rate in spec['rates_per_s']:
 for wq in spec['disturbances_m_s2']:
  for step in map(F,spec['resolutions_s']):
   for method in spec['methods']:
    tail=f'__{method}__r{rate}__w{int(F(wq)*100):02d}__dt{int(step*1000000)}us.csv.gz'
    paths=[B/'traces'/(c+tail) for c in ['return_generous','return_tight']]
    if method!='fir_checked':assert sha(paths[0])==sha(paths[1]);identity+=1
    else:
     rows=[]
     for p in paths:
      with gzip.open(p,'rt') as f:rows.append([r for r in csv.DictReader(f) if F(r['time_exact'])<=F(31,50)])
     assert len(rows[0])==len(rows[1])
     fields=['time_exact','side','q','qv','qa','reference_jerk','x','v','a','u','actual_jerk','truth','x_minus_q','x_minus_truth']
     assert all(all(a[k]==b[k] for k in fields) for a,b in zip(*rows));prefixes+=1
out={'status':'PASS','histories':8,'bound_FIR_polynomial_pieces':fir_count,'native_profile_plan_bindings':native_count,
 'native_generous_inputs_exports_equal_moving08':True,'identical_contrast_trace_pairs':identity,
 'checked_FIR_prefix_pairs_equal_through_062':prefixes,'native_clock_offsets_exact':sorted(set(clock_diffs)),
 'independent_candidate_outcomes':outcomes,'scope':'Input, reference, candidate selection and retained-state binding. Physical replay and native executable checks are separate.'}
(HERE/'bindings-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
