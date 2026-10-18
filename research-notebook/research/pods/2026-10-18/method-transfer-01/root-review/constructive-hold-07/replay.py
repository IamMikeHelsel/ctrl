#!/usr/bin/env python3
"""Fresh local closure, axiom audit, separate kernel, and semantic negatives.
All writes stay in this milestone. No cached local LeanControls oleans are used.
Only the existing pinned package artifacts are reused.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
REVIEW=Path(__file__).resolve().parent;WORK=REVIEW.parents[5];HERE=REVIEW.parents[1]/'controls/constructive-hold-07';BASE=WORK/'lean-controls'
FRESH=REVIEW/'fresh-replay';LOG=REVIEW/'verification-logs'
MODS=['DigitalHold','WeightedEntry','ClearancePolicy','ClearanceAdmission','AdaptiveAdmission','DelayedEntry','ClearanceEntry','AdaptiveWitness','ClearanceWitness','DelayedWitness','ConstructiveClock','ConstructiveFlow','ConstructiveHold','ConstructiveWitness']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 manifest=HERE/'frozen-manifest.json'
 assert manifest.is_file(),'Builder must be frozen before independent replay.'
 frozen=manifest.read_bytes(); expected=json.loads(frozen)['files']
 def preserve_builder():
  assert manifest.read_bytes()==frozen
  assert all(sha(HERE/f)==h for f,h in expected.items())
 preserve_builder()
 (REVIEW/'builder-manifest.json').write_bytes(frozen)
 FRESH.mkdir(exist_ok=True);LOG.mkdir(exist_ok=True)
 assert not list(FRESH.iterdir()),'Use a new replay directory; preserve previous evidence.'
 sources={m:(HERE if m.startswith('Constructive') else HERE/'inputs')/(m+'.lean') for m in MODS}
 original={m:sha(p) for m,p in sources.items()}
 for row in json.loads((HERE/'INPUTS.json').read_text()):
  assert sha(WORK/row['source'])==sha(HERE/row['copy'])==row['sha256']
 records=[
  (HERE.parent/'milestone-01/frozen-manifest.json','86a05aa25625d1054a2213a3599b703d31db5341e365f0e5a79e020dfd937186'),
  (HERE.parent/'finite-entry-02/frozen-manifest.json','c78f5b409eda906a36efeb1b73cf3f75bbecef83bcdf9764eb8c4dd3d46ee52e'),
  (HERE.parent/'adaptive-admission-03/frozen-manifest.json','7d56bd57f0a340107ad04e2c3b0e06aa7a11329757fa241598845294a58a302a'),
  (HERE.parent/'delayed-entry-04/frozen-manifest.json','529bc733f386713d74eb2bfe039b945b5a339b41f9c5afffeb43bf997ad9e5ea'),
  (HERE.parent/'clearance-policy-05/frozen-manifest.json','ca1aa5fd23f1f0d9e3456237712fa90f2c5093a0eb2e1bc63c4b546e4b427691'),
  (HERE.parent/'detector-bridge-06/frozen-manifest.json','133ccaf800b1699c2f126cfaf12d65ec63f460681a3a9de58607eb5d37c8313b')]
 def preserve():
  for p,h in records:
   assert sha(p)==h
   d=json.loads(p.read_text());assert all(sha(p.parent/f)==v for f,v in d['files'].items())
  for row in json.loads((HERE/'PREFLIGHT-SOURCES.json').read_text()):assert sha(WORK/row['source'])==row['sha256']
 preserve()
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
 prior=json.loads((HERE.parent/'milestone-01/verification.json').read_text())
 assert {n:sha(p) for n,p in core.items()}==prior['core_source_sha256']
 for n,p in {**core,**sources}.items():
  dst=FRESH/Path(n.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
 graph={m:re.findall(r'^(?:public |private )?import (\S+)',p.read_text(),re.M) for m,p in sources.items()}
 assert all(n.startswith('Mathlib.') or n in sources or n in core for deps in graph.values() for n in deps)
 for p in sources.values():assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text()),p
 env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan');lake=str(WORK/'.tools/elan/bin/lake')
 def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
 lean=Path(query('which','lean'));checker=lean.with_name('leanchecker')
 paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
 paths=[p for p in paths if '.lake/packages/' in p];assert paths
 assert str(BASE/'.lake/build/lib/lean') not in paths
 env['LEAN_PATH']=str(FRESH)+':'+':'.join(paths);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 report={'passed':False,'scope':'All local LeanControls dependencies and fourteen research modules are copied byte-for-byte and rebuilt. Only pinned package artifacts are reused. No downloaded corpus code is executed.',
  'source_sha256':original,'research_import_graph':graph,'research_build_order':MODS,'core_source_sha256':{n:sha(p) for n,p in core.items()},'core_build_order':order,
  'preflight_manifest_sha256':sha(preflight),'toolchain':query('lean','--version'),
  'lean_sha256':sha(lean),'leanchecker_sha256':sha(checker),'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),
  'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),'package_revisions':json.loads((BASE/'lake-manifest.json').read_text())['packages'],
  'lean_path':env['LEAN_PATH'],'steps':[],'axioms':{},'verifier_sha256':sha(Path(__file__))}
 for k in ['toolchain','lean_sha256','leanchecker_sha256','lean_toolchain_sha256','lake_manifest_sha256']:assert report[k]==prior[k],k
 def save():(REVIEW/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
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
 (FRESH/'Audit.lean').write_text('import ConstructiveWitness\n'+''.join('#print axioms '+n+'\n' for n in names))
 run('axiom-audit',[lean,FRESH/'Audit.lean'])
 for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOG/'axiom-audit.log').read_text()):
  a={s.strip() for s in body.split(',') if s.strip()};assert a<={'propext','Classical.choice','Quot.sound'},(n,a)
  report['axioms'][n]=sorted(a)
 assert set(report['axioms'])==set(names);save()
 for n in order+MODS:run('kernel-'+n,[checker,n,'-v'])
 negative=REVIEW/'negative-controls';negative.mkdir(exist_ok=True)
 mutations=[
  ('ReadCurrentInsteadOfPriorNode','ConstructiveFlow','(measure m ε f n))','(measure m ε f (n+1)))'),
  ('ResetCellToInitialState','ConstructiveFlow','(f (grid (n+1)))','(f 0)'),
  ('WrongCellRateIndex','ConstructiveHold','else R (index b t+1)','else R (index b t)'),
  ('DropIncomingPendingEndpoint','ConstructiveHold','if b then t<h else t≤h','if b then t<h else t<h')]
 for label,mod,old,new in mutations:
  raw=sources[mod].read_text();assert old in raw
  p=negative/(label+'.lean');p.write_text(raw.replace(old,new,1))
  run('reject-'+label,[lean,'--root='+str(negative),p],True)
 claims={
  'FalseIncomingStamp':"""import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : stamp false (grid 2)=h := by
 have hs := second_dispatch_stamps.1
 norm_num [hs] 
""",
  'FalseFinalOutgoingStamp':"""import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : stamp false (grid 4)=grid 3 := by
 have hs := final_dispatch_stamps.1
 rw [hs]
 norm_num [grid]
""",
  'FalseRateContinuity':"""import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : field (fun _ _ => 8) rates false (grid 2)=field (fun _ _ => 8) rates true (grid 2) := by
 rw [actual_rate_and_error_jump.1,actual_rate_and_error_jump.2.1]
 norm_num
""",
  'FalseCommandContinuity':"""import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : LeanControls.ClearanceAdmission.actualCommand h (LeanControls.ClearanceAdmission.center m) (readings m noise run) false h=
 LeanControls.ClearanceAdmission.actualCommand h (LeanControls.ClearanceAdmission.center m) (readings m noise run) true h := by
 rw [first_command_jump.1,first_command_jump.2]
 norm_num
""",
  'FalseStartupStateReset':"""import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : run h 2=run 0 2 := by
 have hs := changed_startup_state
 linarith
""",
  'FalseOneMillisecondPeriod':"""import ConstructiveWitness
example : (1/1000:ℝ)+(1/2000)≤1/1000 := by norm_num
"""}
 for label,body in claims.items():
  p=negative/(label+'.lean');p.write_text(body)
  run('reject-'+label,[lean,p],True)
 preserve();preserve_builder();report['builder_frozen_manifest_preserved']=True;report['builder_manifest_sha256']=sha(manifest);report['prior_frozen_inputs_preserved']=True
 report['source_unchanged']=all(sha(p)==original[m] and sha(FRESH/(m+'.lean'))==original[m] for m,p in sources.items())
 report['core_source_unchanged']=all(sha(p)==report['core_source_sha256'][m] and sha(FRESH/Path(m.replace('.','/')+'.lean'))==sha(p) for m,p in core.items())
 report['old_inputs_preserved']=all(sha(WORK/r['source'])==r['sha256'] for r in json.loads((HERE/'INPUTS.json').read_text()))
 report['preflight_preserved']=all(sha(HERE.parent/r['path'])==r['sha256'] for r in json.loads(preflight.read_text())['entries'])
 report['passed']=all(report[k] for k in ['source_unchanged','core_source_unchanged','old_inputs_preserved','preflight_preserved']) and all(s['passed'] for s in report['steps'])
 save();print(json.dumps({'passed':report['passed'],'core_modules':len(core),'research_modules':len(MODS),'audited_declarations':len(names),'steps':len(report['steps'])}),flush=True)
if __name__=='__main__':main()
