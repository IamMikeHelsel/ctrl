#!/usr/bin/env python3
"""Exact match of frozen06 primary outputs to pre-existing independent oracle."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import json,hashlib,datetime
H=Path(__file__).resolve().parent;B=H.parent/'builder';O=H.parents[1]/'latency-noise-05/builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
expected='1265a245321b006be7ca60c30b7c5cff697dc48b70ff799e0b7c59f857d04dd1'
assert sha(B/'pre-run-implementation-manifest.json')==expected
m=load(B/'pre-run-implementation-manifest.json');assert not m['plant_runs_started'];assert all(sha(B/n)==v for n,v in m['files'].items())
snapshot=load(H/'oracle-before-primary-manifest.json');assert all(sha(H/n)==v for n,v in snapshot['files'].items())
oracle=load(H/'native-oracle.json');assert oracle['all_passed_fixed_limits']
exports=load(B/'ruckig-primary-exports.json');schedules={(s['case'],s['method']):s for s in load(B/'reference-schedules.json')['schedules']};old={(s['case'],s['method']):s for s in load(O/'reference-schedules.json')['schedules']}
assert len(exports)==12 and len(schedules)==24
for n in ['packets.json','observation-times.json','admission-transcripts.json','fir-ablation-equality.json','fir-exact-enclosures.json']:assert (B/n).read_bytes()==(O/n).read_bytes(),n
for key,s in schedules.items():
 if key[1] in ['raw','fir']:assert s==old[key],key
 else:
  for field in ['case','method','hold_required','horizon','horizon_exact','deadline','deadline_exact','truth','common_events','admissions','final_accepted_goal']:assert s[field]==old[key][field],(key,field)
def strip(x):
 if isinstance(x,list):return [strip(z) for z in x]
 if isinstance(x,dict):return {k:strip(v) for k,v in x.items() if k not in ['samples','review_local_checks','input','time_representation','binary_time_metadata']}
 return x
rows=[];sample_count=0;samplemax=[0.]*3;max_clockoffset=Q(0)
for key,plans in exports.items():
 o=oracle['streams'][key];assert len(plans)==len(o['plans']);case,method=key.split('__');s=schedules[case,method]
 for i,(p,q) in enumerate(zip(plans,o['plans'])):
  assert strip(p['plan'])==strip(q['plan']),(key,i,'plan differs')
  commit=q['commit'];tau=Q(commit['time']);stop=Q(o['plans'][i+1]['commit']['time']) if i+1<len(plans) else Q(s['horizon_exact'])
  assert p['native_commit_float']==commit['time'] and Q(p['native_commit_exact'])==tau and float.fromhex(p['native_commit_hex'])==commit['time']
  offset=tau-Q(p['commit_rational']);assert Q(p['native_minus_scheduler_time_exact'])==offset;max_clockoffset=max(max_clockoffset,abs(offset))
  assert Q(p['executed_until_rational'])==stop
  elapsed=float(stop)-commit['time'];assert p['native_elapsed_to_next_commit_or_horizon']==elapsed
  assert p['plan']['input']['state']==[commit[k] for k in ['current_p','current_v','current_a']]
  assert p['plan']['input']['target']==commit['target'];assert p['plan']['input']['queries']==[elapsed]
  for phase in p['plan']['phases']:
   for field,meta in phase['binary_time_metadata'].items():assert Q(meta['ratio'])==Q(phase[field]) and float.fromhex(meta['hex'])==phase[field]
  plan=p['plan'];positive=[z for z in plan['phases'] if z['duration']>0 and z['end']>z['start']]
  for row in plan['samples']:
   t=row['t'];phase=plan['tail'] if t>=plan['duration'] else next(z for z in reversed(positive) if z['start']<=t)
   z=Q(t)-Q(phase['start']);ds=[Q(phase[k]) for k in ['p','v','a','jerk']]
   state=[float(sum((ds[j]*z**(j-k)/factorial(j-k) for j in range(k,4)),Q(0))) for k in range(3)]
   for k,field in enumerate(['p','v','a']):samplemax[k]=max(samplemax[k],abs(state[k]-row[field]))
   sample_count+=1
  assert all(a<=b for a,b in zip(samplemax,[1e-8,1e-8,1e-10]))
 assert len(s['pieces'])==len(o['pieces'])
 for a,b in zip(s['pieces'],o['pieces']):
  for k in ['start_exact','end_exact']:assert Q(a[k])==Q(b[k]),(key,k)
  for k in ['p','v','a','jerk','snap','origin']:assert a[k]==b[k],(key,k)
 rows.append({'key':key,'plans':len(plans),'pieces':len(o['pieces']),'independent_native_queries':o['query_count'],'exact_native_inputs_profiles_and_schedule_match':True,'oracle_max_q_v_a_difference':o['max_q_v_a_difference']})
gate=load(B/'native-pre-run-gate.json');assert gate['passed'] and gate['completed_pairs']==12 and gate['limits_q_v_a']==[1e-8,1e-8,1e-10] and gate['same_input_plans_passed']==492
assert all(x['passed'] and x['native_carried_inputs_and_durations_exactly_equal'] for x in gate['cases'])
assert all(sha(B/n)==v for n,v in m['files'].items())
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'passed':True,'implementation_manifest_sha256':expected,'input_manifest_sha256':sha(B/'pre-run-input-manifest.json'),'independent_oracle_snapshot_sha256':sha(H/'oracle-before-primary-manifest.json'),'all12_primary_native_histories_exactly_match_independent_oracle':True,'all492_primary_native_plans_exactly_match':True,'primary_local_at_time_samples_independently_checked':sample_count,'max_local_q_v_a_difference':samplemax,'raw_FIR_full_schedules_and_all_input_guard_files_byte_preserved':True,'maximum_execution_vs_scheduler_clock_offset_exact':str(max_clockoffset),'maximum_execution_vs_scheduler_clock_offset_s':float(max_clockoffset),'rows':rows,'plant_result_accepted':False,'scope':'Pre-run execution-reference fidelity only; physical replay pending. No global smoothness, bit-identical jerk branches or continuous-runtime theorem.'}
(H/'preflight-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
