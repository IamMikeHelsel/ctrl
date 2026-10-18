#!/usr/bin/env python3
"""Fresh copied local sources, axiom closure, separate kernel, negative controls.
All writes stay in grip-builder/. The fixed Mathlib and LeanControls dependency
artifacts are reused, inventoried and hashed; no toolchain pin is changed.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[4];BASE=WORK/'lean-controls'
ALLOWED={'propext','Classical.choice','Quot.sound'}
MODULES=['ComparisonEnvelope','FirstStop','StoppingCertificate','ActualStop','Recovery','RecoveryWitness']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan');lake=str(WORK/'.tools/elan/bin/lake')
 def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
 lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
 paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
 root=HERE/'fresh-replay';root.mkdir(exist_ok=True)
 for p in root.rglob('*'):
  if p.is_file():p.unlink()
 env['LEAN_PATH']=str(root)+':'+':'.join(paths);env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
 sources={m:(HERE if m.startswith('Recovery') else HERE/'inputs')/(m+'.lean') for m in MODULES}
 originals={m:sha(p) for m,p in sources.items()}
 preflight=json.loads((HERE/'preflight-inputs.json').read_text())['input_sha256']
 for m in MODULES[:4]:
  assert originals[m]==preflight['research/adjacent-controls/variable-response/'+m+'.lean']
  assert originals[m]==sha(WORK/'research/adjacent-controls/variable-response'/(m+'.lean'))
 for p in sources.values():assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text())
 logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
 core_sources={str(p.relative_to(WORK)):sha(p) for p in sorted((BASE/'LeanControls').rglob('*.lean'))}
 core_oleans={str(p.relative_to(WORK)):sha(p) for p in sorted((BASE/'.lake/build/lib/lean/LeanControls').rglob('*.olean'))}
 manifest=json.loads((BASE/'lake-manifest.json').read_text())
 report={'passed':False,'scope':'Six local proof modules are built from fresh copied sources. Imported LeanControls and Mathlib artifacts retain their current fixed pins and are reused. The local LeanControls source/artifact inventory is bound, not claimed rebuilt. Kernel checks replay all six local modules independently.',
  'source_sha256':originals,'verifier_sha256':sha(Path(__file__)),
  'toolchain':query('lean','--version'),'lean_sha256':sha(Path(lean)),'leanchecker_sha256':sha(Path(checker)),
  'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),
  'mathlib_manifest_pin':next(p for p in manifest['packages'] if p['name']=='mathlib'),
  'lean_path':env['LEAN_PATH'],'cached_core_source_sha256':core_sources,'cached_core_olean_sha256':core_oleans,
  'steps':[],'axioms':{}}
 def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
 def run(label,args,negative=False):
  start=time.monotonic()
  with (logs/(label+'.log')).open('w') as out:
   p=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
  raw=(logs/(label+'.log')).read_text();ok=p.returncode!=0 if negative else p.returncode==0
  if negative:ok=ok and 'error:' in raw and ('unsolved goals' in raw or 'linarith failed' in raw) and 'unknownIdentifier' not in raw and 'unknown module' not in raw
  report['steps'].append({'label':label,'exit_code':p.returncode,'passed':ok,'expected':'rejection' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(logs/(label+'.log'))})
  save();print(label,p.returncode,ok,flush=True)
  if not ok:raise RuntimeError(label)
 names=[]
 for m,p in sources.items():
  shutil.copy2(p,root/p.name)
  run('fresh-build-'+m,[lean,'--root='+str(root),'-o',str(root/(m+'.olean')),str(root/p.name)])
  raw=p.read_text();ns=re.search(r'^namespace (\S+)',raw,re.M).group(1)
  names.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',raw,re.M))
 names.extend(['LeanControls.UncertainLag.exact_initial','LeanControls.UncertainLag.exact_ode'])
 (root/'Audit.lean').write_text('import RecoveryWitness\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
 run('axiom-audit',[lean,str(root/'Audit.lean')])
 for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
  ax={x.strip() for x in raw.split(',') if x.strip()};assert ax<=ALLOWED,(name,ax);report['axioms'][name]=sorted(ax)
 assert set(report['axioms'])==set(names),set(names)-set(report['axioms'])
 save()
 for m in MODULES:run('kernel-'+m,[checker,m,'-v'])
 negative=HERE/'negative-controls';negative.mkdir(exist_ok=True);raw=sources['Recovery'].read_text()
 mutations=[('LossTargetControl','(hq : ∀ t ∈ Icc 0 T, q t ≤ A)','(hq : ∀ t ∈ Icc 0 T, q t ≤ A+1)'),('RecoveryAuthorityControl','(hq : ∀ t ∈ Icc 0 S, q t ≤ -b)','(hq : ∀ t ∈ Icc 0 S, q t ≤ 0)')]
 for label,old,new in mutations:
  assert raw.count(old)==1
  p=negative/(label+'.lean');p.write_text(raw.replace(old,new));run('reject-'+label,[lean,'--root='+str(negative),str(p)],True)
 false_claims={
  'CoastStopsControl':'import Recovery\nopen LeanControls.Recovery\nexample : ∃ t : ℝ, coast t 1 ≤ 0 := by\n  norm_num [coast]\n',
  'OldClearanceControl':'import Recovery\nopen LeanControls.Recovery\nexample : (1/1000:ℝ)+travelBudget (41/100) (1/10) (1/20) (6/5) 8 ≤ 3/20 := by\n  norm_num [travelBudget, velocityBudget]\n'}
 for label,txt in false_claims.items():
  p=negative/(label+'.lean');p.write_text(txt);run('reject-'+label,[lean,str(p)],True)
 report['source_unchanged']=all(sha(p)==originals[m] for m,p in sources.items())
 report['copied_helpers_match_originals']=all(sha(WORK/'research/adjacent-controls/variable-response'/(m+'.lean'))==originals[m] for m in MODULES[:4])
 report['preflight_preserved']=all(sha(HERE/f)==h for f,h in json.loads((HERE/'preflight-manifest.json').read_text())['files'].items())
 report['passed']=report['source_unchanged'] and report['copied_helpers_match_originals'] and report['preflight_preserved'] and all(s['passed'] for s in report['steps'])
 save();print(json.dumps({'passed':report['passed'],'audited_declarations':len(names)}),flush=True)
if __name__=='__main__':main()
