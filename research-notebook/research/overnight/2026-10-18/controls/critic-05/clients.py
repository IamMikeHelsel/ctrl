#!/usr/bin/env python3
from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess,sys,time
HERE=Path(__file__).resolve().parent
cfg=json.loads((HERE/'environment.json').read_text())
env=os.environ.copy();env.update(cfg['env']);BUILD=Path(cfg['build'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
attempt=sys.argv[1] if len(sys.argv)>1 else '01'
attempt_dir=HERE/('client-attempt-'+attempt);attempt_dir.mkdir(exist_ok=False)
source=HERE/'ReviewClients.lean'
shutil.copyfile(source,attempt_dir/'ReviewClients.lean')
dest=BUILD/'ReviewClients.lean';shutil.copyfile(source,dest)
log=attempt_dir/'build.log'
with log.open('w') as out:
 p=subprocess.run([cfg['lean'],'--root='+str(BUILD),'-o',str(dest.with_suffix('.olean')),str(dest)],cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
print(log.read_text());print('client_exit',p.returncode)
if p.returncode:sys.exit(p.returncode)
result={'passed':False,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'positive_source_sha256':sha(source),'steps':[]}
def run(label,args,negative=False):
 path=HERE/'logs'/(label+'.log');start=time.monotonic()
 with path.open('w') as out:
  proc=subprocess.run(args,cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
 text=path.read_text();ok=proc.returncode!=0 if negative else proc.returncode==0
 if negative:ok=ok and 'unsolved goals' in text and '⊢ False' in text and not any(s in text for s in ['unknown','failed to synthesize','object file'])
 result['steps'].append({'label':label,'exit':proc.returncode,'passed':ok,'seconds':time.monotonic()-start,'log_sha256':sha(path)})
 (HERE/'clients.json').write_text(json.dumps(result,indent=2)+'\n')
 print(label,proc.returncode,flush=True)
 if not ok:print(text)
 assert ok,label
audit='''import ReviewClients
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if env.allImportedModuleNames[idx.toNat]! == `ReviewClients then
        if info.isUnsafe || info.isAxiom then throwError m!"UNSAFE OR AXIOM: {n}"
        let used ← collectAxioms n
        for ax in used do
          unless allowed.contains ax do throwError m!"UNAPPROVED AXIOM {ax} IN {n}"
        logInfo m!"DECL|{n}|{used}"
'''
(HERE/'ClientAudit.lean').write_text(audit);(BUILD/'ClientAudit.lean').write_text(audit)
run('client-axiom-audit',[cfg['lean'],str(BUILD/'ClientAudit.lean')])
run('kernel-ReviewClients',[cfg['checker'],'ReviewClients','-v'])
negative={
 'exact-rest':'''example : residualMotion (171/50) 1 = 0 := by
  have h := residual_terminal_speed_nonzero
  simp_all
''',
 'omit-initial-cube-speed':'''example : |largeInitial 2 1| ≤ 1/1000 := by
  norm_num [largeInitial]
''',
 'omit-initial-cube-acceleration':'''example : |largeInitial 2 2| ≤ 1/50 := by
  norm_num [largeInitial]
''',
 'erase-negative-bias':'''example : biasedReference (-1/100) (71/50) 0 = 0 := by
  rw [negative_bias_is_not_reset]
  norm_num
''',
 'shorten-terminal-deadline':'''example : (171/50:ℝ) ≤ 17/10 := by norm_num
''',
 'erase-initial-coordinate':'''example : coordinates 0 (scaledError 10 residualMotion
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) 0 = 0 := by
  norm_num [residualMotion,coordinates,scaledError,scaleState,error,referenceState]
''',
 'wrong-clock-trajectory':'''example : ¬ ¬ IsTrajectory 2 changingRate
      (fun s => holdInput 10 0 (fun u => biasedReference (1/200) (71/50+u)) s +
        changingDisturbance s)
      (fun s => biasedReference (1/200) (71/50+s)) := by
  simp only [not_not,wrong_clock_is_not_trajectory]
''',
 'force-rate-constant':'''example : changingRate 0 = changingRate 2 := by
  norm_num [changingRate]
''',
}
header='''import ReviewClients
open Set LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.TrackingReplan LeanControls.Settling
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness ControlsReview05
noncomputable section
'''
nd=HERE/'negative-controls';nd.mkdir(exist_ok=True)
for label,code in negative.items():
 p=nd/(label+'.lean');p.write_text(header+code)
 run('reject-review-'+label,[cfg['lean'],str(p)],True)
for p in sorted((HERE.parent/'builder-05/negative-controls').glob('*.lean')):
 run('reject-builder-'+p.stem,[cfg['lean'],str(p)],True)
result['positive_theorems']=sum(1 for line in source.read_text().splitlines() if line.startswith('theorem '))
result['audited_client_declarations']=sum(1 for line in (HERE/'logs/client-axiom-audit.log').read_text().splitlines() if line.startswith('DECL|'))
result['new_false_clients']=len(negative);result['inherited_false_clients']=6
result['passed']=all(s['passed'] for s in result['steps'])
result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(HERE/'clients.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
