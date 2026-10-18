#!/usr/bin/env python3
"""Independent numeric counter-control for the invalid rate-floor shortcut."""
from pathlib import Path
import json,hashlib,os,subprocess,time
HERE=Path(__file__).resolve().parent;OUT=HERE/'grip';FRESH=OUT/'fresh';LOG=OUT/'logs'
r=json.loads((OUT/'replay-results.json').read_text());lean=Path(r['steps'][0]['command'][0]);checker=lean.with_name('leanchecker')
env=os.environ.copy();env['LEAN_PATH']=r['lean_path'];env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
sources={'CriticRateComparison.lean': 'import Recovery\nnamespace IndependentRecoveryCritic\n-- q=-1, a=-2, actual rate r=2, lower rate k=1, b=1.\nexample : (2:ℝ)*(-1-(-2)) > -(1:ℝ)*((-2)+1) := by norm_num\nexample : ¬ ((2:ℝ)*(-1-(-2)) ≤ -(1:ℝ)*((-2)+1)) := by norm_num\nend IndependentRecoveryCritic\n', 'RejectActualAccelerationShortcut.lean': 'import Recovery\nexample : (2:ℝ)*(-1-(-2)) ≤ -(1:ℝ)*((-2)+1) := by norm_num\n'}
for n,s in sources.items():(FRESH/n).write_text(s)
steps=[]
for label,args,negative in [
 ('critic-rate-comparison',[lean,'--root='+str(FRESH),'-o',FRESH/'CriticRateComparison.olean',FRESH/'CriticRateComparison.lean'],False),
 ('kernel-CriticRateComparison',[checker,'CriticRateComparison','-v'],False),
 ('reject-actual-acceleration-shortcut',[lean,FRESH/'RejectActualAccelerationShortcut.lean'],True)]:
 start=time.monotonic();p=LOG/(label+'.log')
 with p.open('w') as out:a=subprocess.run(list(map(str,args)),cwd=FRESH,env=env,stdout=out,stderr=subprocess.STDOUT)
 raw=p.read_text();ok=a.returncode==0 if not negative else a.returncode!=0 and 'error:' in raw and 'unsolved goals' in raw and 'unknown' not in raw.lower()
 steps.append({'label':label,'command':list(map(str,args)),'exit_code':a.returncode,'passed':ok,'expected':'mathematical rejection' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(p)})
 print(label,a.returncode,ok,flush=True)
 assert ok,label
(OUT/'extra-checks.json').write_text(json.dumps({'passed':all(s['passed'] for s in steps),'steps':steps,'script_sha256':sha(Path(__file__)),'source_sha256':{n:sha(FRESH/n) for n in ['CriticRateComparison.lean','RejectActualAccelerationShortcut.lean']}},indent=2)+'\n')
