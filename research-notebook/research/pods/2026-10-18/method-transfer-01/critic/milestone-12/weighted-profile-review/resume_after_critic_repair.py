"""Resume only critic/audit/kernel/negative checks after preserved tactic error.
A full clean reproduction uses replay.py with the final CriticControls.lean.
This script binds and reuses the five unchanged successful source builds.
"""
import replay as R
from pathlib import Path
from datetime import datetime,timezone
import json,re,os,subprocess,time,shutil
H,W=R.HERE,R.WORK
attempt=H/'attempts/critic-moment-unfold'
for rel,h in json.loads((attempt/'manifest.json').read_text()).items():assert R.sha(attempt/rel)==h,rel
for rel,h in json.loads((attempt/'compiled-products.json').read_text()).items():assert R.sha(H/rel)==h,rel
data=json.loads((attempt/'verification.json').read_text())
assert len(data['runs'])==6 and all(x['passed'] for x in data['runs'][:5]) and not data['runs'][5]['passed']
data['initial_failed_attempt']={'manifest_sha256':R.sha(attempt/'manifest.json'),'path':str(attempt.relative_to(H)),'failed_step':'compile-CriticControls','repair':'Unfold weightedMean before rewriting degrees; theorem statements unchanged.'}
data['runs']=data['runs'][:5]
for row in data['runs']:
 row['reused_from_preserved_attempt']=True
 row['log_sha256']=R.sha(H/row['log'])
data['audit_format_failed_attempt']={'path':'attempts/axiom-universe-format','manifest_sha256':R.sha(H/'attempts/axiom-universe-format/manifest.json'),'repair':'Strip displayed universe suffixes from axiom constant names; retain raw audit output and raw names.'}
data['resumed_utc']=datetime.now(timezone.utc).isoformat()
for mod in R.MODULES[:5]:
 s=data['sources'][mod];assert R.sha(H/s['copy'])==R.sha(H/s['input'])==s['sha256'],mod
shutil.copyfile(H/'CriticControls.lean',W/'CriticControls.lean')
data['sources']['CriticControls']['sha256']=R.sha(H/'CriticControls.lean')
env=os.environ.copy();env['LEAN_PATH']=data['lean_path'];env['PATH']=str(R.BIN)+os.pathsep+env.get('PATH','')
def save():(H/'verification.json').write_text(json.dumps(data,indent=2)+'\n')
def run(label,args,negative=False):
 t=time.monotonic()
 try:
  r=subprocess.run(args,cwd=W,env=env,capture_output=True,text=True,timeout=180)
  out=r.stdout+r.stderr;rc=r.returncode
 except subprocess.TimeoutExpired as e:out=str(e.stdout or '')+'\n'+str(e.stderr or '')+'\nTIMEOUT';rc=124
 (W/(label+'.log')).write_text(out)
 ok=rc==0 if not negative else rc not in [0,124] and 'unsolved goals' in out and not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize',out)
 data['runs'].append({'label':label,'command':args,'returncode':rc,'expected_rejection':negative,'passed':bool(ok),'seconds':time.monotonic()-t,'log':'fresh/'+label+'.log'})
 save();print(label,rc,ok,flush=True)
 if not ok:raise RuntimeError(label)
 return out
run('compile-CriticControls',[str(R.BIN/'lean'),'-o','CriticControls.olean','CriticControls.lean'])
out=run('compile-ReviewAudit',[str(R.BIN/'lean'),'-o','ReviewAudit.olean','ReviewAudit.lean'])
axes={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
axes.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",out)})
assert set(axes)==set(data['declarations'])
data['axioms_raw']=axes
axes={n:[re.sub(r'\.\{[^{}]*\}$','',x) for x in vals] for n,vals in axes.items()}
assert all(set(x)<=R.ALLOWED for x in axes.values())
data['axioms']=axes;save()
for mod in R.MODULES+['ReviewAudit']:run('kernel-'+mod.replace('.','-'),[str(R.BIN/'leanchecker'),mod,'-v'])
for name in ['BadTriangle','BadMean','BadNormalization','BadBranch']:
 src=R.INPUT/'evidence/fresh-source-w0h5n10v'/f'{name}.lean';shutil.copyfile(src,W/src.name)
 run('reject-'+name,[str(R.BIN/'lean'),src.name],True)
(W/'BadZeroDegreeHighMean.lean').write_text('''import CriticControls
open Erdos128 Erdos128.ProfileBridge Erdos128.ProfileControls CriticE8
example : weightedMean singletonWeight (highProfile emptyGraph singletonWeight (4 / 5) 0) = 4 / 5 := by
  rw [zero_degree_high_mean]
  norm_num
''')
run('reject-BadZeroDegreeHighMean',[str(R.BIN/'lean'),'BadZeroDegreeHighMean.lean'],True)
for rel,h in json.loads((R.INPUT/'artifact-sha256.json').read_text())['files'].items():assert R.sha(R.INPUT/rel)==h
for mod,s in data['sources'].items():assert R.sha(H/s['input'])==s['sha256']==R.sha(H/s['copy']),mod
data['artifact_hashes']={str(p.relative_to(W)):R.sha(p) for p in W.rglob('*') if p.is_file() and any(x in p.name for x in ['.olean','.ilean','.ir'])}
data['source_hashes_stable']=True;data['completed_utc']=datetime.now(timezone.utc).isoformat();data['passed']=True;save()
print('PASS',len(data['runs']),'steps',len(data['axioms']),'closures',flush=True)
