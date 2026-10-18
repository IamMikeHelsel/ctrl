#!/usr/bin/env python3
"""Independent input-to-reference bindings for frozen moving08 data; no runs."""
from fractions import Fraction as F
from pathlib import Path
from math import comb,factorial
import json,hashlib
HERE=Path(__file__).resolve().parent;B=HERE.parent.parent/'moving-goal-08/builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((B/n).read_text())
manifest=read('data-sha256.json');assert sha(B/'data-sha256.json')=='c4714051bd9ddf0c44f6e64eef7cf83b35c40494db5be11b10c8ae4cdb171fb3'
assert all(sha(B/n)==h for n,h in manifest['files'].items())
spec=read('packets.json');ss=read('reference-schedules.json')['schedules'];tt=read('admission-transcripts.json')['cases']
assert spec['methods']==['ruckig','ruckig_min_08','fir'] and spec['rates_per_s']==[80,100,120]
assert spec['disturbances_m_s2']==['0','1/100'] and spec['resolutions_s']==['1/1000','1/2000']
lookup={(s['case'],s['method']):s for s in ss};trans={(t['case'],t['method']):t for t in tt}
count_native=count_fir=0;clock_diffs=[]
for case in spec['cases']:
 assert case['end_s']=='5/2' and case['revision_issue_s']=='1/2'
 for method in spec['methods']:
  key=(case['id'],method);s=lookup[key];tr=trans[key];assert s['task_spec']==case
  assert len(s['admissions'])==2 and s['admissions']==tr['outcomes']
  for packet,o in zip(case['packets'],s['admissions']):
   assert all(o[k]==v for k,v in packet.items())
   c=-(-F(packet['ready_s'])//F(1,50))*F(1,50);tau=c+F(case['buffer_s'])
   assert F(o['admission_s'])==c and F(o['execution_s'])==tau
   assert c>=F(packet['ready_s'])>=F(packet['observed_s'])
  assert [F(p['end_exact']) for p in s['pieces'][:-1]]==[F(p['start_exact']) for p in s['pieces'][1:]]
  assert F(s['pieces'][0]['start_exact'])==0 and F(s['pieces'][-1]['end_exact'])==F(5,2)
  if method=='fir':
   events=[tuple(map(F,e)) for e in tr['events']];h=F(1,5)
   for p in s['pieces']:
    l,r=map(F,[p['start_exact'],p['end_exact']]);mid=(l+r)/2
    ds=[]
    for d in range(5):
     ds.append(sum((amp*(-1)**k*comb(4,k)*(l-tau-k*h)**(4-d)/factorial(4-d)/h**4
       for tau,amp in events for k in range(5) if tau+k*h<mid),F(0)))
    assert list(map(F,p['rational_derivatives_at_start']))==ds
    assert [p[k] for k in ['p','v','a','jerk','snap']]==list(map(float,ds))
    count_fir+=1
  else:
   stem='__'.join(key);records=read('native-plans/'+stem+'-output.json')
   md=.8 if method=='ruckig_min_08' else 0.
   assert records['minimum_duration']==md and len(records['plans'])==2
   inputlines=(B/'native-plans'/(stem+'-input.txt')).read_text().splitlines()
   assert int(inputlines[0])==2
   expected=[];last=F(0)
   for i,(o,record,line) in enumerate(zip(s['admissions'],records['plans'],inputlines[1:])):
    tau=float(F(o['execution_s']));target=float(F(o['target_m']));assert list(map(float,line.split()))==[tau,target]
    assert record['native_commit']==tau and record['target']==target and o['outcome']=='accepted'
    origin=F(tau);stop=F(float(F(s['admissions'][i+1]['execution_s']))) if i==0 else F(5,2)
    assert s['execution_clock_records'][i]['actual_exact']==str(origin)
    clock_diffs.append(str(origin-F(o['execution_s'])))
    plan=record['plan'];assert plan['minimum_duration']==md
    if i==0:
     assert record['current_state']==[0,0,0]
     expected.append((F(0),origin,[0.,0.,0.,0.,0.],'initial_rest'))
    else:
     prev=records['plans'][i-1];elapsed=tau-prev['native_commit']
     assert prev['native_elapsed_to_next_commit_or_horizon']==elapsed
     samples=[q for q in prev['plan']['samples'] if q['t']==elapsed]
     assert samples and all([q[k] for k in ['p','v','a']]==record['current_state'] for q in samples)
    for phase in plan['phases']:
     if phase['duration']<=0:continue
     start=origin+F(phase['start']);end=min(stop,origin+F(phase['end']))
     if start<end:expected.append((start,end,[phase[k] for k in ['p','v','a','jerk']]+[0.],f'plan_{i}_{phase["kind"]}_{phase["index"]}'))
    tail=plan['tail'];start=origin+F(tail['start'])
    if start<stop:expected.append((start,stop,[tail[k] for k in ['p','v','a','jerk']]+[0.],f'plan_{i}_extrapolated_tail'))
    count_native+=1
   actual=[(F(p['start_exact']),F(p['end_exact']),[p[k] for k in ['p','v','a','jerk','snap']],p['origin']) for p in s['pieces']]
   assert actual==expected,stem
for method in spec['methods']:
 a,b=[lookup[(case,method)] for case in ['return_generous','return_predelivery']]
 assert all(a[k]==b[k] for k in ['pieces','truth','common_events'])
identities=[]
for r in read('A-B-physical-identity.json'):
 stem=f"__{r['method']}__r{r['rate']}__w{int(F(r['disturbance'])*100):02d}__dt{int(F(r['step'])*1000000)}us.csv.gz"
 a,b=[B/'traces'/(case+stem) for case in ['return_generous','return_predelivery']]
 assert sha(a)==sha(b)==r['trace_sha256'];identities.append(r)
gate=read('native-pre-run-gate.json')
assert gate['passed'] and gate['completed_pairs']==8 and gate['same_input_plans_passed']==16
assert gate['limits_q_v_a']==[1e-8,1e-8,1e-10]
for r in gate['cases']:
 assert r['passed'] and r['native_carried_inputs_and_durations_exactly_equal']
 assert all(x<=y for x,y in zip(r['reference_max_abs_q_v_a'],gate['limits_q_v_a']))
assert all(sha(B/n)==h for n,h in manifest['files'].items())
out={'passed':True,'manifest_sha256':sha(B/'data-sha256.json'),'frozen_files':len(manifest['files']),
 'input_bound_histories':len(ss),'independently_bound_FIR_polynomial_pieces':count_fir,
 'native_input_and_profile_plan_bindings':count_native,'A_B_identical_trace_pairs':len(identities),
 'native_clock_minus_rational_time_exact':sorted(set(clock_diffs)),
 'saved_native_gate_queries':sum(r['queries'] for r in gate['cases']),
 'scope':'Independent exact input/profile/schedule binding plus audit of saved native gate. No new native executable run in this script. Physical replay is separate; native firmware is not verified.'}
(HERE/'schedule-binding-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
