#!/usr/bin/env python3
"""Run after replay_controls.py; retain main evidence unchanged."""
from pathlib import Path
import os,json,hashlib,subprocess,time,re,shutil
HERE=Path(__file__).resolve().parent;FRESH=HERE/'fresh';LOG=HERE/'extra-logs';LOG.mkdir(exist_ok=True)
assert not (HERE/'extra-results.json').exists(),'Preserve prior accepted/failed result.'
main=json.loads((HERE/'replay-results.json').read_text());assert main['passed']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=Path(main['steps'][0]['command'][0]);checker=lean.with_name('leanchecker')
env=os.environ.copy();env['LEAN_PATH']=main['lean_path'];env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
r={'passed':False,'main_result_sha256':sha(HERE/'replay-results.json'),'runner_sha256':sha(Path(__file__)),'steps':[],'axioms':{}}
for name in ['RateAndClockScope.lean','FalseFloorOnlyFace.lean']:shutil.copy2(HERE/name,FRESH/name)
r['sources']={n:sha(HERE/n) for n in ['RateAndClockScope.lean','FalseFloorOnlyFace.lean']}
def save():(HERE/'extra-results.json').write_text(json.dumps(r,indent=2)+'\n')
def run(label,args,neg=False):
 p=LOG/(label+'.log');t=time.monotonic()
 with p.open('w') as out:q=subprocess.run(list(map(str,args)),cwd=FRESH,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
 raw=p.read_text();ok=q.returncode==0
 if neg:ok=q.returncode!=0 and 'error:' in raw and ('linarith failed' in raw or 'unsolved goals' in raw) and not any(s in raw.lower() for s in ['unknown identifier','unknown module','no such file'])
 r['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':q.returncode,'passed':ok,'expected':'semantic rejection' if neg else 'success','seconds':round(time.monotonic()-t,4),'log_sha256':sha(p)})
 save();print(label,q.returncode,ok,flush=True);assert ok,label
run('build-rate-clock-scope',[lean,'--root='+str(FRESH),'-o',FRESH/'RateAndClockScope.olean',FRESH/'RateAndClockScope.lean'])
(FRESH/'AuditExtra.lean').write_text('import RateAndClockScope\n#print axioms CriticC4.floor_only_face_outward\n#print axioms CriticC4.second_dispatch_stamps\n#print axioms CriticC4.second_dispatch_total_age\n')
run('audit-rate-clock-scope',[lean,FRESH/'AuditExtra.lean'])
for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOG/'audit-rate-clock-scope.log').read_text()):
 a={s.strip() for s in body.split(',') if s.strip()};assert a<={'propext','Classical.choice','Quot.sound'};r['axioms'][n]=sorted(a)
assert len(r['axioms'])==3;save()
run('kernel-rate-clock-scope',[checker,'RateAndClockScope','-v'])
run('reject-false-floor-only-face',[lean,FRESH/'FalseFloorOnlyFace.lean'],True)
r['passed']=all(s['passed'] for s in r['steps']);save();print('extra passed',r['passed'],flush=True)
