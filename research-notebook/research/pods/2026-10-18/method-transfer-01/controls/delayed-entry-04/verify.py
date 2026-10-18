#!/usr/bin/env python3
"""Fresh complete local C4 closure, axiom audit, kernel replay and negatives.
All writes stay here. The complete local closure is six modules; the copied
DigitalHold module has only Mathlib imports. Package products retain their pin.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5];BASE=WORK/'lean-controls'
MODS=['DigitalHold','AdaptiveAdmission','WeightedEntry','DelayedEntry','AdaptiveWitness','DelayedWitness']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def preserved():
 records=[
  (HERE.parent/'PREFLIGHT-MANIFEST.json','e87a250aff21e22ac7377a012ce6a282e016316484fc73b954a4ff1c23b6d8d9'),
  (HERE.parent/'milestone-01/frozen-manifest.json','86a05aa25625d1054a2213a3599b703d31db5341e365f0e5a79e020dfd937186'),
  (HERE.parent/'finite-entry-02/frozen-manifest.json','c78f5b409eda906a36efeb1b73cf3f75bbecef83bcdf9764eb8c4dd3d46ee52e'),
  (HERE.parent/'adaptive-admission-03/frozen-manifest.json','7d56bd57f0a340107ad04e2c3b0e06aa7a11329757fa241598845294a58a302a'),
  (WORK/'research/pods/2026-10-18/recovery-handoff-02/handoff-builder/artifact-sha256.json','0ca3f54c0d77ff244866bb5a861c6d701749594d6d155c87ba9ab7338e23276e')]
 for p,h in records:
  assert sha(p)==h
  d=json.loads(p.read_text())
  pairs=d['files'].items() if 'files' in d else [(e['path'],e['sha256']) for e in d['entries']]
  assert all(sha(p.parent/f)==v for f,v in pairs)
 for row in json.loads((HERE/'INPUTS.json').read_text()):
  assert sha(WORK/row['source'])==row['sha256']
  assert sha(HERE/row['copy'])==row['sha256']
 assert sha(HERE/'inputs/DigitalHold.lean')=='aa91b649affc0906c79dd7a017b34d6f729d1c16f50117ab87daaa1ed2fadc03'
def main():
 preserved()
 root=HERE/'fresh-replay';root.mkdir(exist_ok=True);assert not list(root.iterdir())
 logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
 sources={m:(HERE if m in ['DelayedEntry','DelayedWitness'] else HERE/'inputs')/(m+'.lean') for m in MODS}
 original={m:sha(p) for m,p in sources.items()}
 imports={m:re.findall(r'^public import (\S+)',p.read_text(),re.M) for m,p in sources.items()}
 assert all(n.startswith('Mathlib.') or n in sources for imps in imports.values() for n in imps)
 order=[]
 def visit(m):
  if m in order:return
  for n in imports[m]:
   if n in sources:visit(n)
  order.append(m)
 visit('DelayedWitness');assert order==MODS
 for m,p in sources.items():
  assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text()),p
  shutil.copy2(p,root/p.name)
 env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan');lake=str(WORK/'.tools/elan/bin/lake')
 def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
 lean=Path(query('which','lean'));checker=lean.with_name('leanchecker')
 paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
 paths=[p for p in paths if '.lake/packages/' in p];assert paths
 assert str(BASE/'.lake/build/lib/lean') not in paths
 env['LEAN_PATH']=str(root)+':'+':'.join(paths);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 report={'passed':False,'scope':'Complete local closure: DigitalHold, AdaptiveAdmission, WeightedEntry, DelayedEntry, AdaptiveWitness, DelayedWitness. All six fresh-built and separately kernel-checked. No cached local proof product or corpus code is imported. Pinned external package artifacts are reused.',
  'source_sha256':original,'local_import_graph':imports,'local_build_order':order,'toolchain':query('lean','--version'),
  'lean_sha256':sha(lean),'leanchecker_sha256':sha(checker),'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),
  'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),'package_revisions':json.loads((BASE/'lake-manifest.json').read_text())['packages'],
  'lean_path':env['LEAN_PATH'],'verifier_sha256':sha(Path(__file__)),'steps':[],'axioms':{}}
 prior=json.loads((HERE.parent/'milestone-01/verification.json').read_text())
 for k in ['toolchain','lean_sha256','leanchecker_sha256','lean_toolchain_sha256','lake_manifest_sha256']:assert report[k]==prior[k],k
 def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
 def run(label,args,negative=False):
  start=time.monotonic();p=logs/(label+'.log')
  with p.open('w') as out:r=subprocess.run(list(map(str,args)),cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
  raw=p.read_text()
  ok=r.returncode==0 if not negative else r.returncode!=0 and 'error:' in raw and any(s in raw for s in ['unsolved goals','linarith failed','Type mismatch','Application type mismatch']) and not any(s in raw.lower() for s in ['unknown identifier','unknown module','no such file'])
  report['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':r.returncode,'passed':ok,'expected':'semantic rejection' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(p)})
  save();print(label,r.returncode,ok,flush=True);assert ok,label
 names=[]
 for m in order:
  p=root/(m+'.lean');run('build-'+m,[lean,'--root='+str(root),'-o',p.with_suffix('.olean'),p])
  raw=p.read_text();ns=re.search(r'^namespace (\S+)',raw,re.M).group(1)
  names.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',raw,re.M))
 (root/'Audit.lean').write_text('import DelayedWitness\n'+''.join('#print axioms '+n+'\n' for n in names))
 run('axiom-audit',[lean,root/'Audit.lean'])
 for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
  a={s.strip() for s in body.split(',') if s.strip()};assert a<={'propext','Classical.choice','Quot.sound'},(n,a)
  report['axioms'][n]=sorted(a)
 assert set(report['axioms'])==set(names);save()
 for m in order:run('kernel-'+m,[checker,m,'-v'])
 negative=HERE/'negative-controls';negative.mkdir(exist_ok=True)
 mutations=[
  ('WiderResidual','DelayedEntry','def residual : ℝ := 111/1000','def residual : ℝ := 3/25'),
  ('FiveMillisecondAge','AdaptiveAdmission','t-stamp b t ≤ 1/1000','t-stamp b t ≤ 1/200')]
 for label,m,old,new in mutations:
  raw=sources[m].read_text();assert raw.count(old)==1
  p=negative/(label+'.lean');p.write_text(raw.replace(old,new));run('reject-'+label,[lean,'--root='+str(negative),p],True)
 claims={
  'FalseEarlyDeadline':"""import DelayedWitness
open LeanControls.DelayedEntry LeanControls.DelayedEntry.Witness LeanControls.WeightedEntry
example : envelope delay entryTime ≤ target := by
 have h := deadline_requires_delay
 linarith
""",
  'FalseDigitalLeftAtDispatch':"""import DelayedWitness
open LeanControls
example : AdaptiveAdmission.actualCommand DelayedEntry.Witness.delay
    (AdaptiveAdmission.center (DelayedEntry.Witness.reading 0))
    (fun _ _ => DelayedEntry.Witness.reading 0) false DelayedEntry.Witness.delay = 0 := by
 have h := (DelayedEntry.Witness.dispatch_command_sides 0).1
 linarith
""",
  'FalsePendingResidual':"""import DelayedWitness
open LeanControls
example : |AdaptiveAdmission.actualMismatch DelayedEntry.Witness.delay
    (DelayedEntry.Witness.reading 0) (DelayedEntry.Witness.state 0)
    (fun _ _ => 0) (fun _ _ => DelayedEntry.Witness.reading 0) false 0| ≤ DelayedEntry.residual := by
 have h := DelayedEntry.Witness.pending_mismatch_is_not_digital_budget 0
 linarith
""",
  'FalseResetCausality':"""import DelayedWitness
open LeanControls.DelayedEntry.Witness
example : 0 ≤ stamp false delay-delay := by
 have h := illegal_reset_makes_negative_stamp
 linarith
""",
  'FalseWholeHorizonClearance15':"""import DelayedWitness
open LeanControls
example : AdaptiveAdmission.center AdaptiveAdmission.exampleReading+DigitalHold.radius ≤ 3/20 := by
 norm_num [AdaptiveAdmission.center,AdaptiveAdmission.exampleReading,DigitalHold.radius]
""",
  'FalseRenewedAge':"""import DelayedWitness
example : (1:ℝ)/500-0 ≤ 1/1000 := by norm_num
"""}
 for label,body in claims.items():
  p=negative/(label+'.lean');p.write_text(body);run('reject-'+label,[lean,p],True)
 preserved();report['prior_frozen_inputs_preserved']=True
 report['source_unchanged']=all(sha(p)==original[m] and sha(root/(m+'.lean'))==original[m] for m,p in sources.items())
 report['passed']=report['source_unchanged'] and all(s['passed'] for s in report['steps'])
 save();print(json.dumps({'passed':report['passed'],'local_modules':len(order),'audited_closures':len(names),'steps':len(report['steps'])}),flush=True)
if __name__=='__main__':main()
