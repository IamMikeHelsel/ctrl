#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_right
from math import factorial
import json,gzip,hashlib,subprocess,sys,datetime
H=Path(__file__).resolve().parent;B=H.parent/'builder';OLD=H.parents[1]/'latency-noise-05/builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
assert len(sys.argv)==2;expected=sys.argv[1];assert sha(B/'artifact-sha256.json')==expected
manifest=load(B/'artifact-sha256.json');assert all(sha(B/n)==v for n,v in manifest['files'].items())
for f in ['pre-run-input-manifest.json','pre-run-implementation-manifest.json']:
 assert all(sha(B/n)==v for n,v in load(B/f)['files'].items())
pre=load(H/'preflight-review.json');execution=load(B/'execution-record.json');assert sha(H/'preflight-review.json')==execution['preflight_report_sha256']
assert pre['checked_utc']<execution['plant_running_observed_utc'];assert execution['plant_exit_code']==0
source=load(OLD/'ruckig-provenance.json');native=OLD/'.cache/native_replay';assert sha(native)==source['native_replay_executable_sha256']
schedules={(s['case']+'__'+s['method']):s for s in load(B/'reference-schedules.json')['schedules']}
results=[];limits=[1e-8,1e-8,1e-10]
for key,s in schedules.items():
 if s['method'] not in ['ruckig','ruckig_min_08']:continue
 minimum=.8 if s['method']=='ruckig_min_08' else 0.;input_text=(B/'native-checks'/(key+'-input.txt')).read_text()
 out=subprocess.check_output([str(native),str(minimum)],input=input_text,text=True);fresh=json.loads(out)
 with gzip.open(B/'native-checks'/(key+'-output.json.gz'),'rt') as f:saved=json.load(f)
 assert fresh==saved,(key,'independent native replay differs')
 with (H/(key+'-final-native.json.gz')).open('wb') as f:
  with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:z.write(out.encode())
 pieces=s['pieces'];starts=[Q(p['start_exact']) for p in pieces];maxima=[0.]*3;branches=[]
 for row in fresh['queries']:
  t=Q(row['time']);i=max(0,min(bisect_right(starts,t)-1,len(pieces)-1));p=pieces[i];z=t-starts[i];d=[Q(p[k]) for k in ['p','v','a','jerk','snap']]
  ref=[float(sum((d[j]*z**(j-k)/factorial(j-k) for j in range(k,5)),Q(0))) for k in range(4)]
  for k,f in enumerate(['q','qv','qa']):maxima[k]=max(maxima[k],abs(ref[k]-row[f]))
  if ref[3]!=row['jerk']:branches.append({'time':row['time'],'native_jerk':row['jerk'],'polynomial_jerk':ref[3],'nearest_boundary_distance_s':float(min(abs(t-x) for x in starts))})
 assert all(a<=b for a,b in zip(maxima,limits))
 results.append({'key':key,'native_queries_independently_replayed':len(fresh['queries']),'native_commits':len(fresh['commits']),'native_output_exactly_matches_frozen_builder':True,'max_q_v_a_discrepancy':maxima,'fixed_q_v_a_limits_passed':True,'jerk_branch_differences':branches})
assert len(results)==12
old_manifest=load(OLD/'artifact-sha256.json');assert sha(OLD/'artifact-sha256.json')=='8266eb7bd4da50d20f8fce651100126df1c9876b223c94a28d67c610fa3f4f78';assert all(sha(OLD/n)==v for n,v in old_manifest['files'].items())
oldgrader=OLD.parent/'grader';og=load(oldgrader/'artifact-sha256.json');assert sha(oldgrader/'artifact-sha256.json')=='3c1c1d16f17e40ba92e9f240031040ea03dc45dda1a881cc03f3ff62d8fde45d';assert all(sha(oldgrader/n)==v for n,v in og['files'].items())
prior=load(OLD/'preservation.json');assert all(sha(OLD.parents[1]/n)==v for n,v in prior['prior_files'].items())
assert all(sha(B/n)==v for n,v in manifest['files'].items()) and sha(B/'artifact-sha256.json')==expected
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'passed':True,'builder_manifest_sha256':expected,'builder_files_checked':len(manifest['files']),'rows':results,'total_native_queries_independently_replayed':sum(x['native_queries_independently_replayed'] for x in results),'all12_fixed_state_checks_passed':True,'independent_preflight_verified_before_plant':True,'builder_unchanged':True,'05_builder646_files_and_grader104_files_unchanged':True,'older379_files_unchanged':True,'scope':'Finite native q/v/a reconstruction plus source and preservation review. Not a continuous-runtime or jerk-branch equivalence proof.'}
(H/'final-fidelity-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
