#!/usr/bin/env python3
"""Fresh closure and all-declaration audit; independent review remains separate."""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,tempfile,time
import dev
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
TARGETS=['ComparisonEnvelope','ScaledTracking','Composition','PhysicalArrival','Settling','SettlingFixtures','QuadraticAlgebra','QuadraticTrajectory','FIRHold','FIRHoldWitness']
NEGATIVES={
'unshifted-physical-inputs':'''import FIRHoldWitness
open RobotMotion.FIRHoldWitness
example : wrongClockRHS = 0 := by
  rw [wrong_clock_rhs_nonzero]
  norm_num
''',
'erase-inherited-state':'''import FIRHoldWitness
open RobotMotion.FIRHoldWitness
example : biasedReference (1/100) (71/50) 0 = 0 := by
  rw [biased_endpoint_not_reset]
  norm_num
''',
'wrong-reference-clock':'''import FIRHoldWitness
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness
example : position 0 (1/5) (realEvents deferredReturn) (1/2) = 0 := by
  rw [wrong_clock_is_nonzero]
  norm_num
''',
'exact-physical-arrival':'''import FIRHoldWitness
open RobotMotion.FIRHoldWitness
example : |biasedReference (1/100) (171/50) 0| ≤ 0 := by
  rw [biased_terminal_not_exact_goal]
  norm_num
''',
'drop-wait-before-speed-band':'''import FIRHoldWitness
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness
example : |biasedReference (1/100) (1/2) 1| ≤ 1/1000 := by
  norm_num [biasedReference,velocity,response,realEvents,realEvent,deferredReturn,F1,P]
''',
'erase-initial-error':'''import FIRHoldWitness
open LeanControls.RobustHold LeanControls.ScaledTracking
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness
example : coordinates 0 (scaledError 10 (biasedReference (1/100))
    (referenceState 0 (1/5) (realEvents deferredReturn)) 0) 0 = 0 := by
  rw [initial_error_not_erased]
  norm_num
'''}
def main():
 env,lean,dep=dev.environment();checker=str(Path(lean).with_name('leanchecker'))
 sources=dev.source_closure();assert all(p.exists() for p in sources.values())
 source_manifest={m:{'path':str(p.relative_to(dev.WORK)),'sha256':sha(p),'bytes':p.stat().st_size} for m,p in sources.items()}
 for p in sources.values():
  code=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
  assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',code),p
 inherited=json.loads((HERE/'inherited-sources.json').read_text())
 for m,v in inherited.items():assert sha(HERE/'inherited'/(m.replace('.','/')+'.lean'))==v['sha256'],m
 (HERE/'source-closure.json').write_text(json.dumps(source_manifest,indent=2)+'\n')
 logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
 mathlib=dev.BASE/'.lake/packages/mathlib'
 report={'passed':False,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Fresh local sources; pinned Mathlib cache reused. All imported local declarations audited, including private declarations. Fresh source and separate kernel replay are not independent review.','sources':source_manifest,'steps':[],
 'toolchain':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),
 'lean_toolchain_file':(dev.BASE/'lean-toolchain').read_text().strip(),
 'mathlib_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip(),
 'mathlib_status':subprocess.check_output(['git','status','--porcelain'],cwd=mathlib,text=True),
 'lake_manifest_sha256':sha(dev.BASE/'lake-manifest.json'),
 'verifier_sha256':sha(Path(__file__)),'helper_sha256':sha(HERE/'dev.py')}
 assert report['toolchain'].startswith('Lean (version 4.35.0'),report['toolchain']
 assert report['mathlib_revision']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
 def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
 def run(label,args,cwd,renv,negative=False):
  log=logs/(label+'.log');start=time.monotonic()
  with log.open('w') as out:proc=subprocess.run(args,cwd=cwd,env=renv,stdout=out,stderr=subprocess.STDOUT,timeout=600)
  ok=proc.returncode!=0 if negative else proc.returncode==0
  report['steps'].append({'label':label,'exit_code':proc.returncode,'passed':ok,'seconds':time.monotonic()-start,'log_sha256':sha(log)})
  save();print(label,proc.returncode,flush=True);assert ok,label
 with tempfile.TemporaryDirectory(prefix='fresh-',dir=HERE) as tmp:
  root=Path(tmp);renv=env.copy();renv['LEAN_PATH']=str(root)+':'+dep
  renv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
  for m,p in sources.items():
   dst=root/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
   run('build-'+m,[lean,'--root='+str(root),'-o',str(dst.with_suffix('.olean')),str(dst)],root,renv)
  audit='''import FIRHoldWitness
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let owned : Array Name := #[OWNED]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx.toNat]!
      if owned.contains mod then
        if info.isUnsafe then throwError "unsafe local declaration {n}"
        if info.isAxiom then throwError "local axiom {n}"
        let used ← collectAxioms n
        for ax in used do
          unless allowed.contains ax do throwError "unapproved axiom {ax} in {n}"
        logInfo m!"DECL|{mod}|{n}|{info.isTheorem}|{used}"
'''.replace('OWNED',','.join('`'+m for m in sources))
  (HERE/'EnvironmentAudit.lean').write_text(audit);(root/'EnvironmentAudit.lean').write_text(audit)
  run('all-local-axiom-audit',[lean,str(root/'EnvironmentAudit.lean')],root,renv)
  rows=[x for x in (logs/'all-local-axiom-audit.log').read_text().splitlines() if x.startswith('DECL|')]
  report['all_local_declaration_count']=len(rows)
  report['audited_modules']=sorted({x.split('|')[1] for x in rows})
  assert set(report['audited_modules'])==set(sources)
  for m in TARGETS:run('kernel-'+m,[checker,m,'-v'],root,renv)
  controls=HERE/'negative-controls';controls.mkdir(exist_ok=True)
  for label,code in NEGATIVES.items():
   (controls/(label+'.lean')).write_text(code)
   p=root/(label.replace('-','_')+'.lean');p.write_text(code)
   run('reject-'+label,[lean,str(p)],root,renv,negative=True)
   output=(logs/('reject-'+label+'.log')).read_text()
   assert 'error: unknown' not in output and 'unsolved goals' in output and '⊢ False' in output,(label,output)
 report['source_unchanged']=all(sha(p)==source_manifest[m]['sha256'] for m,p in sources.items())
 report['fresh_local_module_count']=len(sources)
 report['kernel_modules']=TARGETS;report['negative_count']=len(NEGATIVES)
 report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 report['passed']=report['source_unchanged'] and all(x['passed'] for x in report['steps']);save()
 print(json.dumps({'passed':report['passed'],'modules':len(sources),'declarations':report['all_local_declaration_count'],'kernels':len(TARGETS),'negative_count':len(NEGATIVES)}))
if __name__=='__main__':main()
