#!/usr/bin/env python3
"""Independent native history and exact-binary absolute-clock polynomial oracle.
Uses only frozen05 inputs and pinned executables. No plant state is simulated.
"""
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_right
from math import factorial,ceil,nextafter,inf
import json,gzip,hashlib,subprocess
H=Path(__file__).resolve().parent;O=H.parents[1]/'latency-noise-05/builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(n):return json.loads((O/n).read_text())
def dump(n,x):(H/n).write_text(json.dumps(x,indent=2)+'\n')
assert sha(O/'artifact-sha256.json')=='8266eb7bd4da50d20f8fce651100126df1c9876b223c94a28d67c610fa3f4f78'
manifest=load('artifact-sha256.json');assert all(sha(O/n)==v for n,v in manifest['files'].items())
prov=load('ruckig-provenance.json');native=O/'.cache/native_replay';exporter=O/'.cache/ruckig_export'
assert sha(native)==prov['native_replay_executable_sha256'];assert sha(exporter)==prov['executable_sha256']
spec=load('packets.json');tick=Q(spec['commit_tick_s']);limits=[1e-8,1e-8,1e-10]
result={'status':'running','source_builder_manifest_sha256':sha(O/'artifact-sha256.json'),'native_executable_sha256':sha(native),'exporter_sha256':sha(exporter),'clock':'Exact binary absolute native commit value plus exact binary native cumulative phase boundary; native retained state from C++ at_time with double absolute-time subtraction.','fixed_q_v_a_limits':limits,'streams':{}}
def query_native(commits,times,minimum):
 text=str(len(commits))+'\n'+'\n'.join(format(t,'.17g')+' '+format(g,'.17g') for t,g in commits)+'\n'+str(len(times))+'\n'+'\n'.join(format(t,'.17g') for t in times)+'\n'
 return json.loads(subprocess.check_output([str(native),str(minimum)],input=text,text=True))
for case in spec['cases']:
 groups={}
 for p in case['packets']:groups.setdefault(ceil(Q(p['ready_s'])/tick)*tick,[]).append(p)
 commits=[(float(t),float(Q(max(ps,key=lambda p:p['sequence'])['target_m']))) for t,ps in sorted(groups.items())]
 for method,minimum in [('ruckig',0.),('ruckig_min_08',.8)]:
  key=case['id']+'__'+method;history=query_native(commits,[],minimum);assert [(x['time'],x['target']) for x in history['commits']]==commits
  plans=[];pieces=[{'start_exact':'0','end_exact':str(Q(commits[0][0])),'p':0.,'v':0.,'a':0.,'jerk':0.,'snap':0.,'origin':'initial_rest'}];collapsed=[]
  for i,commit in enumerate(history['commits']):
   tau=Q(commit['time']);stop=Q(commits[i+1][0]) if i+1<len(commits) else Q(case['end_s'])
   state=[commit[k] for k in ['current_p','current_v','current_a']]
   args=[str(exporter)]+[format(x,'.17g') for x in [*state,commit['target'],minimum]]
   plan=json.loads(subprocess.check_output(args,text=True));assert plan['duration']==commit['duration'];assert plan['accel_duration']==0
   probes={0.,plan['duration'],plan['duration']+.01}
   for phase in plan['phases']:
    if phase['duration']<=0:continue
    probes.update([phase['start'],phase['end'],(phase['start']+phase['end'])/2])
    for t in [phase['start'],phase['end']]:
     if t>0:probes.add(nextafter(t,0.));probes.add(nextafter(t,inf))
   probes=sorted(t for t in probes if t>=0 and (t==0 or t>=1e-300))
   queried=json.loads(subprocess.check_output(args+[format(t,'.17g') for t in probes],text=True))
   assert {k:v for k,v in queried.items() if k!='samples'}=={k:v for k,v in plan.items() if k!='samples'}
   localmax=[0.]*3;positive=[p for p in plan['phases'] if p['duration']>0 and p['end']>p['start']]
   for row in queried['samples']:
    t=row['t'];phase=plan['tail'] if t>=plan['duration'] else next(p for p in reversed(positive) if p['start']<=t)
    z=Q(t)-Q(phase['start']);d=[Q(phase[k]) for k in ['p','v','a','jerk']]
    computed=[float(sum((d[i]*z**(i-k)/factorial(i-k) for i in range(k,4)),Q(0))) for k in range(3)]
    for j,field in enumerate(['p','v','a']):localmax[j]=max(localmax[j],abs(computed[j]-row[field]))
   assert all(a<=b for a,b in zip(localmax,limits)),(key,i,localmax)
   plan['review_local_checks']={'queries':len(probes),'max_q_v_a_difference':localmax,'passed_fixed_limits':True}
   plans.append({'commit':commit,'plan':plan})
   for p in plan['phases']:
    if p['duration']<=0:continue
    start=tau+Q(p['start']);end=min(stop,tau+Q(p['end']))
    if start>=stop:continue
    if end<=start:
     collapsed.append({'plan_index':i,'phase':p,'absolute_start':str(start),'absolute_end':str(end)});continue
    pieces.append({'start_exact':str(start),'end_exact':str(end),**{k:p[k] for k in ['p','v','a','jerk']},'snap':0.,'origin':f'plan_{i}_{p["kind"]}_{p["index"]}'})
   if tau+Q(plan['duration'])<stop:
    p=plan['tail'];pieces.append({'start_exact':str(tau+Q(p['start'])),'end_exact':str(stop),**{k:p[k] for k in ['p','v','a','jerk']},'snap':0.,'origin':f'plan_{i}_extrapolated_tail'})
  starts=[Q(p['start_exact']) for p in pieces];ends=[Q(p['end_exact']) for p in pieces];assert starts[0]==0 and ends[-1]==Q(case['end_s']) and ends[:-1]==starts[1:]
  times={float(Q(k,2000)) for k in range(int(Q(case['end_s'])*2000)+1)}
  for boundary in starts+ends:
   t=float(boundary);times.add(t)
   if t>0:times.add(nextafter(t,0));times.add(nextafter(t,inf))
  times=sorted(t for t in times if 0<=t<=float(Q(case['end_s'])));replay=query_native(commits,times,minimum);assert replay['commits']==history['commits']
  maxima=[0.]*3;worst=[None]*3;branches=[]
  for row in replay['queries']:
   t=Q(row['time']);ix=max(0,min(bisect_right(starts,t)-1,len(pieces)-1));p=pieces[ix];z=t-starts[ix];ds=[Q(p[k]) for k in ['p','v','a','jerk','snap']]
   ref=[float(sum((ds[i]*z**(i-k)/factorial(i-k) for i in range(k,5)),Q(0))) for k in range(4)]
   for j,field in enumerate(['q','qv','qa']):
    d=abs(row[field]-ref[j])
    if d>maxima[j]:maxima[j]=d;worst[j]={'time':row['time'],'native':row[field],'polynomial':ref[j],'difference':d}
   if ref[3]!=row['jerk']:branches.append({'time':row['time'],'native_jerk':row['jerk'],'polynomial_jerk':ref[3],'nearest_boundary_distance_s':float(min(abs(t-b) for b in starts+ends))})
  with (H/(key+'-oracle-native.json.gz')).open('wb') as f:
   with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:z.write(json.dumps(replay,separators=(',',':')).encode())
  entry={'plans':plans,'pieces':pieces,'positive_phases_with_collapsed_cumulative_interval':collapsed,'query_count':len(times),'max_q_v_a_difference':maxima,'worst_q_v_a':worst,'jerk_branch_differences':branches,'passed_fixed_limits':all(a<=b for a,b in zip(maxima,limits))}
  result['streams'][key]=entry;dump('native-oracle.json',result);print(key,entry['passed_fixed_limits'],maxima,'collapsed',len(collapsed),flush=True)
result['all_passed_fixed_limits']=all(x['passed_fixed_limits'] for x in result['streams'].values());result['source_unchanged']=all(sha(O/n)==v for n,v in manifest['files'].items());result['status']='complete';dump('native-oracle.json',result)
print('all_passed',result['all_passed_fixed_limits'],flush=True)
