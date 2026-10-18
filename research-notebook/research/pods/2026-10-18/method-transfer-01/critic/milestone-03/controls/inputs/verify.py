#!/usr/bin/env python3
"""Fresh local closure, axiom audit, separate kernel, and semantic negatives.
All writes stay in this milestone. No cached local LeanControls oleans are used.
Only the existing pinned package artifacts are reused.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5];BASE=WORK/'lean-controls'
FRESH=HERE/'fresh-replay';LOG=HERE/'verification-logs'
MODS=['ComparisonEnvelope','FirstStop','StoppingCertificate','ActualStop','Recovery','RecoveryPeak','RecoveryPeakWitness']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 FRESH.mkdir(exist_ok=True);LOG.mkdir(exist_ok=True)
 assert not list(FRESH.iterdir()),'Use a new replay directory; preserve previous evidence.'
 sources={m:(HERE if m.startswith('RecoveryPeak') else HERE/'inputs')/(m+'.lean') for m in MODS}
 original={m:sha(p) for m,p in sources.items()}
 for row in json.loads((HERE/'INPUTS.json').read_text()):
  assert sha(WORK/row['source'])==sha(HERE/row['copy'])==row['sha256']
 preflight=HERE.parent/'PREFLIGHT-MANIFEST.json'
 assert sha(preflight)=='e87a250aff21e22ac7377a012ce6a282e016316484fc73b954a4ff1c23b6d8d9'
 for row in json.loads(preflight.read_text())['entries']:assert sha(HERE.parent/row['path'])==row['sha256']
 core={};order=[]
 def visit(n):
  if n in core:return
  p=BASE/Path(n.replace('.','/')+'.lean');core[n]=p
  for line in re.findall(r'^(?:public |private )?import (.+)$',p.read_text(),re.M):
   for imp in line.split():
    if imp.startswith('LeanControls.'):visit(imp)
  order.append(n)
 visit('LeanControls.UncertainLag')
 for n,p in {**core,**sources}.items():
  dst=FRESH/Path(n.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
 for p in sources.values():assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text()),p
 env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan');lake=str(WORK/'.tools/elan/bin/lake')
 def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
 lean=Path(query('which','lean'));checker=lean.with_name('leanchecker')
 paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
 paths=[p for p in paths if '.lake/packages/' in p];assert paths
 assert str(BASE/'.lake/build/lib/lean') not in paths
 env['LEAN_PATH']=str(FRESH)+':'+':'.join(paths);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 report={'passed':False,'scope':'All local LeanControls dependencies and seven research modules are copied byte-for-byte and rebuilt. Only pinned package artifacts are reused. No downloaded corpus code is executed.',
  'source_sha256':original,'core_source_sha256':{n:sha(p) for n,p in core.items()},'core_build_order':order,
  'preflight_manifest_sha256':sha(preflight),'toolchain':query('lean','--version'),
  'lean_sha256':sha(lean),'leanchecker_sha256':sha(checker),'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),
  'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),'package_revisions':json.loads((BASE/'lake-manifest.json').read_text())['packages'],
  'lean_path':env['LEAN_PATH'],'steps':[],'axioms':{},'verifier_sha256':sha(Path(__file__))}
 def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
 def run(label,args,negative=False):
  start=time.monotonic();p=LOG/(label+'.log')
  with p.open('w') as out:r=subprocess.run(list(map(str,args)),cwd=FRESH,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
  raw=p.read_text()
  if negative:
   ok=r.returncode!=0 and 'error:' in raw and any(s in raw for s in ['unsolved goals','linarith failed','Type mismatch','Application type mismatch']) and not any(s in raw.lower() for s in ['unknown identifier','unknown module','no such file'])
  else:ok=r.returncode==0
  report['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':r.returncode,'passed':ok,'expected':'semantic rejection' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(p)})
  save();print(label,r.returncode,ok,flush=True)
  assert ok,label
 for n in order+MODS:
  p=FRESH/Path(n.replace('.','/')+'.lean')
  run('build-'+n,[lean,'--root='+str(FRESH),'-o',p.with_suffix('.olean'),p])
 names=[]
 for m,p in sources.items():
  raw=p.read_text();ns=re.search(r'^namespace (\S+)',raw,re.M).group(1)
  names.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',raw,re.M))
 names+=['LeanControls.UncertainLag.exact_initial','LeanControls.UncertainLag.exact_ode']
 (FRESH/'Audit.lean').write_text('import RecoveryPeakWitness\n'+''.join('#print axioms '+n+'\n' for n in names))
 run('axiom-audit',[lean,FRESH/'Audit.lean'])
 for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOG/'axiom-audit.log').read_text()):
  a={s.strip() for s in body.split(',') if s.strip()};assert a<={'propext','Classical.choice','Quot.sound'},(n,a)
  report['axioms'][n]=sorted(a)
 assert set(report['axioms'])==set(names);save()
 for n in order+MODS:run('kernel-'+n,[checker,n,'-v'])
 negative=HERE/'negative-controls';negative.mkdir(exist_ok=True)
 raw=sources['RecoveryPeak'].read_text()
 mutations=[
  ('WeakenLossTarget','(hqLoss : ∀ t ∈ Icc 0 T, qLoss t ≤ A)','(hqLoss : ∀ t ∈ Icc 0 T, qLoss t ≤ A+1)'),
  ('RemoveRecoveredAuthority','(hqBrake : ∀ s ∈ Icc 0 S, qBrake s ≤ -b)','(hqBrake : ∀ s ∈ Icc 0 S, qBrake s ≤ 0)'),
  ('RemoveRecoveredRateFloor','(hrBrake : ∀ s ∈ Icc 0 S, k ≤ rBrake s)','(hrBrake : ∀ s ∈ Icc 0 S, 0 ≤ rBrake s)')]
 for label,old,new in mutations:
  assert raw.count(old)==1
  p=negative/(label+'.lean');p.write_text(raw.replace(old,new))
  run('reject-'+label,[lean,'--root='+str(negative),p],True)
 claims={
  'FalseFourteenCentimetres':'''import RecoveryPeak
open LeanControls.RecoveryPeak LeanControls.UncertainLag
example : heldSolution 8 (12/25) (-6/5) LeanControls.StoppingCertificate.engagementUpper 0 ≤ (7/50:ℝ) := by
 have h := old_upper_exceeds_14cm
 nlinarith
''',
  'FalseSimpleClearance':'''import RecoveryPeak
open LeanControls.Recovery
example : (1/1000:ℝ)+travelBudget (41/100) (1/10) (1/20) (6/5) 8 ≤ 3/20 := by
 norm_num [travelBudget,velocityBudget]
''',
  'FalseMaintainedRest':'''import RecoveryPeakWitness
open LeanControls.RecoveryPeak.Witness LeanControls.UncertainLag
example : heldSolution 1 1 (-1) ![0,0,1] 1 = 0 := by
 have h := zero_speed_not_hold.2.1
 linarith
'''}
 for label,body in claims.items():
  p=negative/(label+'.lean');p.write_text(body)
  run('reject-'+label,[lean,p],True)
 report['source_unchanged']=all(sha(p)==original[m] and sha(FRESH/(m+'.lean'))==original[m] for m,p in sources.items())
 report['core_source_unchanged']=all(sha(p)==report['core_source_sha256'][m] and sha(FRESH/Path(m.replace('.','/')+'.lean'))==sha(p) for m,p in core.items())
 report['old_inputs_preserved']=all(sha(WORK/r['source'])==r['sha256'] for r in json.loads((HERE/'INPUTS.json').read_text()))
 report['preflight_preserved']=all(sha(HERE.parent/r['path'])==r['sha256'] for r in json.loads(preflight.read_text())['entries'])
 report['passed']=all(report[k] for k in ['source_unchanged','core_source_unchanged','old_inputs_preserved','preflight_preserved']) and all(s['passed'] for s in report['steps'])
 save();print(json.dumps({'passed':report['passed'],'core_modules':len(core),'research_modules':len(MODS),'audited_declarations':len(names),'steps':len(report['steps'])}),flush=True)
if __name__=='__main__':main()
