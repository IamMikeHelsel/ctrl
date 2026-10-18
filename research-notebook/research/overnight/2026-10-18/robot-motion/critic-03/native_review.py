"""Fresh native drivers against the pinned library; no builder Python imports."""
from pathlib import Path
from fractions import Fraction as F
from bisect import bisect_right
from math import factorial
import gzip,hashlib,json,subprocess,shutil
HERE=Path(__file__).resolve().parent;B=HERE.parent/'builder-03';WORK=HERE.parents[4]
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
for name in ['native_suffix.cpp','native_queries.cpp','profile_export.hpp']:shutil.copyfile(B/name,N/name)
out={'status':'RUNNING','source_tree_files_checked':len(prior['source_tree_sha256']),'revision':prior['revision'],'library_sha256':sha(lib),'sources':{n:sha(N/n) for n in ['native_suffix.cpp','native_queries.cpp','profile_export.hpp']},'builds':[],'cases':[]}
for name in ['native_suffix','native_queries']:
 cmd=['clang++','-std=c++20','-O2','-I'+str(src/'include'),str(N/(name+'.cpp')),str(lib),'-o',str(N/name)]
 r=subprocess.run(cmd,text=True,capture_output=True)
 (HERE/'logs'/('native-build-'+name+'.log')).write_text(r.stdout+r.stderr)
 assert r.returncode==0,r.stderr
 out['builds'].append({'command':cmd,'exit_code':r.returncode,'executable_sha256':sha(N/name)})
ss=json.loads((B/'reference-schedules.json').read_text())['schedules']
for key,md in [('native_fast','0'),('native_matched','.9')]:
 inputs=(B/'native-plans'/(key+'-input.txt')).read_text()
 initial=list(map(float,inputs.splitlines()[0].split()))
 exact=[F(77,19200),F(23,480),F(5,16),F(0)]
 assert initial==list(map(float,exact))
 r=subprocess.run([str(N/'native_suffix'),md],input=inputs,text=True,capture_output=True,check=True)
 native=json.loads(r.stdout);saved=json.loads((B/'native-plans'/(key+'-export.json')).read_text());assert native==saved
 (HERE/(key+'-fresh-native-plan.json')).write_text(r.stdout)
 r=subprocess.run([str(N/'native_queries'),md],input=inputs,text=True,capture_output=True,check=True)
 queries=json.loads(r.stdout);assert queries==json.loads((B/'native-plans'/(key+'-queries.json')).read_text())
 (HERE/(key+'-fresh-native-queries.json.gz')).write_bytes(gzip.compress(r.stdout.encode(),mtime=0))
 plan=native['plan'];phases=[p for p in plan['phases'] if p['duration']>0]+[plan['tail']]
 s=next(s for s in ss if s['method']==key);pieces=[p for p in s['pieces'] if F(p['start_exact'])>=F(13,25)]
 assert len(pieces)==len(phases)
 for p,q in zip(pieces,phases):
  assert F(p['start_exact'])==F(13,25)+F(q['start'])
  assert all(p[k]==q[k] for k in ['p','v','a','jerk']) and p['snap']==0
  if 'end' in q:assert F(p['end_exact'])==F(13,25)+F(q['end'])
 starts=[F(p['start']) for p in phases];errors=[0.,0.,0.];jerr=0.;branch=0
 for row in queries['queries']:
  t=F(row['t']);idx=bisect_right(starts,t)-1;p=phases[idx];dt=t-starts[idx];ds=[F(p[k]) for k in ['p','v','a','jerk']]
  val=[sum((ds[j]*dt**(j-k)/factorial(j-k) for j in range(k,4)),F(0)) for k in range(4)]
  for i,k in enumerate(['p','v','a']):errors[i]=max(errors[i],abs(row[k]-float(val[i])))
  jerr=max(jerr,abs(row['jerk']-float(val[3])));branch+=row['jerk']!=float(val[3])
 assert len(queries['queries'])==3961 and all(e<1e-10 for e in errors) and branch==0
 if md=='.9':assert plan['duration']==float(F(9,10)) and plan['minimum_duration']==float(F(9,10))
 else:assert plan['minimum_duration']==0 and plan['duration']<.9
 out['cases'].append({'method':key,'exact_initial_qva':list(map(str,exact[:3])),'queries':len(queries['queries']),'plan_equal_saved':True,'queries_equal_saved':True,'exported_piece_and_clock_binding':True,'independent_polynomial_max_qva_errors':errors,'jerk_error':jerr,'branch_mismatches':branch,'duration':plan['duration']})
out['status']='PASS';out['scope']='Pinned native planning and 7922 fresh query calls. Exact rational origin .52 plus binary phase offsets; no hardware or optimal squared-jerk claim.'
(HERE/'native-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
