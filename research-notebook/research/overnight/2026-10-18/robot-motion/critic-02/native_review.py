"""Fresh native drivers against the pinned library; no builder Python imports."""
from pathlib import Path
from fractions import Fraction as F
from bisect import bisect_right
from math import factorial
import gzip,hashlib,json,subprocess,shutil
HERE=Path(__file__).resolve().parent;B=HERE.parent/'builder-02';WORK=HERE.parents[4]
OLD=WORK/'research/pods/2026-10-17/robot-motion/latency-noise-05/builder'
N=HERE/'.cache/native';N.mkdir(parents=True,exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prov=json.loads((B/'native-build-provenance.json').read_text())
prior=json.loads((OLD/'ruckig-provenance.json').read_text())
assert prov['revision']==prior['revision']=='99751e6ebc7c963bb80e99fbbe66f2c279d1db57'
assert not prov['cloud_enabled'] and not prior['cloud_enabled']
src=OLD/'.cache'/('ruckig-'+prior['revision']);lib=OLD/'.cache/build/libruckig.a'
assert sha(lib)==prov['library_sha256']==prior['library_sha256']
for name,digest in prior['source_tree_sha256'].items():assert sha(src/name)==digest,name
for name in ['native_execution.cpp','native_replay.cpp','profile_export.hpp']:shutil.copyfile(B/name,N/name)
out={'status':'RUNNING','source_tree_files_checked':len(prior['source_tree_sha256']),'revision':prior['revision'],'library_sha256':sha(lib),'sources':{n:sha(N/n) for n in ['native_execution.cpp','native_replay.cpp','profile_export.hpp']},'builds':[],'cases':[]}
for name in ['native_execution','native_replay']:
 cmd=['clang++','-std=c++20','-O2','-I'+str(src/'include'),str(N/(name+'.cpp')),str(lib),'-o',str(N/name)]
 r=subprocess.run(cmd,text=True,capture_output=True)
 (HERE/'logs'/('native-build-'+name+'.log')).write_text(r.stdout+r.stderr)
 assert r.returncode==0,r.stderr
 out['builds'].append({'command':cmd,'exit_code':r.returncode,'executable_sha256':sha(N/name)})
ss=json.loads((B/'runtime-replay-02/reference-schedules.json').read_text())['schedules']
for s in ss:
 if not s['method'].startswith('ruckig'):continue
 key=s['case']+'__'+s['method'];md='.8' if s['method']=='ruckig_min_08' else '0'
 inputs=(B/'native-plans'/(key+'-input.txt')).read_text()
 r=subprocess.run([str(N/'native_execution'),md,'2.5'],input=inputs,text=True,capture_output=True,check=True)
 assert json.loads(r.stdout)==json.loads((B/'native-plans'/(key+'-output.json')).read_text())
 (HERE/(key+'-fresh-native-plan.json')).write_text(r.stdout)
 queryinput=(B/'native-checks'/(key+'-input.txt')).read_text()
 r=subprocess.run([str(N/'native_replay'),md],input=queryinput,text=True,capture_output=True,check=True)
 native=json.loads(r.stdout)
 with gzip.open(B/'native-checks'/(key+'-output.json.gz'),'rt') as f:saved=json.load(f)
 assert native==saved
 (HERE/(key+'-fresh-native-queries.json.gz')).write_bytes(gzip.compress(r.stdout.encode(),mtime=0))
 starts=[F(p['start_exact']) for p in s['pieces']]
 errors=[0.,0.,0.];jerk_disagreements=0
 for row in native['queries']:
  t=F(row['time']);idx=min(max(0,bisect_right(starts,t)-1),len(starts)-1);p=s['pieces'][idx];dt=t-starts[idx]
  ds=[F(p[k]) for k in ['p','v','a','jerk','snap']]
  values=[sum((ds[j]*dt**(j-k)/factorial(j-k) for j in range(k,5)),F(0)) for k in range(4)]
  for i,name in enumerate(['q','qv','qa']):errors[i]=max(errors[i],abs(row[name]-float(values[i])))
  if abs(row['jerk']-float(values[3]))>1e-8:jerk_disagreements+=1
 assert all(e<=t for e,t in zip(errors,[1e-8,1e-8,1e-10]))
 out['cases'].append({'case':key,'queries':len(native['queries']),'fresh_exports_exactly_equal_saved':True,'fresh_native_queries_exactly_equal_saved':True,'independent_polynomial_max_q_v_a_errors':errors,'jerk_branch_disagreements':jerk_disagreements})
out['status']='PASS';out['scope']='Finite native fidelity and exact profile binding. No hardware or continuous-runtime proof.'
(HERE/'native-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
