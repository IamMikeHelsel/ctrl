from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time
import dev

HERE=Path(__file__).resolve().parent
ROOT=HERE/'.cache/fresh'
LOGS=HERE/'verification-logs'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def code(s):
    while '/-' in s:
        newer=re.sub(r'/-((?!/-|-/)[\s\S])*?-/', '', s)
        assert newer!=s,'unclosed block comment'
        s=newer
    return re.sub(r'--[^\n]*','',s)

def main():
    assert not ROOT.exists(),'Do not reuse or overwrite proof evidence.'
    ROOT.mkdir(parents=True);LOGS.mkdir(exist_ok=True)
    env,lean,deps=dev.environment();checker=Path(lean).parent/'leanchecker'
    deps=':'.join(x for x in deps.split(':') if Path(x).resolve() != (dev.BASE/'.lake/build/lib/lean').resolve())
    env['LEAN_PATH']=str(ROOT)+':'+deps
    env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    sources=dev.source_closure('VelocityOracle')
    before={m:{'path':str(p.relative_to(dev.WORK)),'sha256':sha(p),'bytes':p.stat().st_size} for m,p in sources.items()}
    (HERE/'source-closure.json').write_text(json.dumps(before,indent=2)+'\n')
    result={'status':'RUNNING','started_at_utc':now(),'sources':before,
      'local_module_count':len(sources),'source_freeze_sha256':sha(HERE/'source-freeze.json'),
      'lean_toolchain':(dev.BASE/'lean-toolchain').read_text().strip(),
      'lake_manifest_sha256':sha(dev.BASE/'lake-manifest.json'),
      'lean_sha256':sha(Path(lean)),'leanchecker_sha256':sha(checker),
      'builds':[],'kernel':[],'negative_controls':[]}
    def save():(HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    def run(args,name,negative=False):
        start=time.monotonic()
        p=subprocess.run(args,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log=LOGS/(name+'.log');log.write_text(p.stdout)
        if negative:
            assert p.returncode!=0 and 'error:' in p.stdout
            assert not any(x in p.stdout for x in ['unknown identifier','unknown constant','object file','unknown module prefix'])
        elif p.returncode:
            print(p.stdout[-12000:],flush=True);raise RuntimeError(name)
        return {'command':args,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,6),
          'log':str(log.relative_to(HERE)),'log_sha256':sha(log)}
    bindings=json.loads((HERE/'input-bindings.json').read_text())
    def check_bindings():
        for v in bindings['sources'].values(): assert sha(dev.WORK/v['path'])==v['sha256']
        for group in ['closure_manifests','toolchain_files']:
            for name,digest in bindings[group].items(): assert sha(dev.WORK/name)==digest
    try:
        check_bindings()
        for m,p in sources.items():
            assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',code(p.read_text())),m
            dst=ROOT/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
            print('BUILD',m,flush=True)
            result['builds'].append({'module':m,**run([lean,'--root='+str(ROOT),'-o',str(dst.with_suffix('.olean')),str(dst)],'build-'+m.replace('.','_'))});save()
        audit='''import VelocityOracle
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
        (HERE/'EnvironmentAudit.lean').write_text(audit);(ROOT/'EnvironmentAudit.lean').write_text(audit)
        result['axiom_audit']=run([lean,'--root='+str(ROOT),str(ROOT/'EnvironmentAudit.lean')],'axiom-audit')
        result['audited_declarations']=(LOGS/'axiom-audit.log').read_text().count('DECL|');save()
        for m in sources:
            print('KERNEL',m,flush=True)
            result['kernel'].append({'module':m,**run([str(checker),m,'-v'],'kernel-'+m)});save()
        negatives={
          'FalseEndpointSufficiency':"""import VelocityFixtures
open RobotMotion.VelocityAdmission
example : (∀ t : ℝ, 0 ≤ t → |RobotMotion.velocity 1 [(0,1),(1,-1)] t| ≤ 1/2) := by
  intro t ht
  have h := interior_real_violation
  have bad : |RobotMotion.velocity 1 [(0,1),(1,-1)] (9/5)| ≤ 1/2 := by
    norm_num [RobotMotion.velocity,RobotMotion.response,RobotMotion.F1,RobotMotion.P]
  exact False.elim (not_le_of_gt h bad)
""",
          'FalseConservativeAcceptance':"""import VelocityFixtures
open RobotMotion.VelocityAdmission
example : checkVelocity 1 (1/6) 0 [(0,1),(1/4,-1)] = true := by
  rw [conservative_rejection]
  norm_num
""",
          'FalseCurrentAcceptance':"""import VelocityFixtures
open RobotMotion.VelocityAdmission
example : checkVelocity 1 0 (7/2) [(0,1)] = true := by
  rw [current_inside_tail_rejected]
  norm_num
""",
          'FalseQueuedAcceptance':"""import VelocityFixtures
open RobotMotion.VelocityAdmission
example : checkVelocity 1 (1/2) 0 [(10,1)] = true := by
  rw [queued_history_rejected]
  norm_num
""",
          'FalseNoSafeRejectedHistory':"""import VelocityFixtures
open RobotMotion.VelocityAdmission
example : ¬ (∀ t : ℝ, 0 ≤ t → |RobotMotion.velocity 1 [(0,1),(1/4,-1)] t| ≤ 1/6) := by
  have good := rejected_history_is_safe
  simp only [good,not_true_eq_false]
  norm_num
""",
          'FalseTightDeadlineSelection':"""import VelocityFixtures
open RobotMotion.VelocityAdmission
example : chooseVelocityExecution (1/5) (1/15) (1/2) (15/2) (13/25) (13/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := by
  rw [tight_deadline_no_candidate]
  norm_num
"""}
        nd=HERE/'negative-controls';nd.mkdir(exist_ok=True)
        for name,text in negatives.items():
            (nd/(name+'.lean')).write_text(text);dst=ROOT/(name+'.lean');dst.write_text(text)
            result['negative_controls'].append({'name':name,**run([lean,'--root='+str(ROOT),str(dst)],'negative-'+name,True)})
        assert all(sha(p)==before[m]['sha256'] for m,p in sources.items())
        freeze=json.loads((HERE/'source-freeze.json').read_text())
        assert all(sha(HERE/n)==v['sha256'] for n,v in freeze['files'].items())
        assert sha(dev.BASE/'lake-manifest.json')==result['lake_manifest_sha256']
        check_bindings()
        result['source_preservation']='PASS'
        objects={str(p.relative_to(ROOT)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in ROOT.rglob('*') if p.is_file() and p.suffix!='.lean'}
        (HERE/'compiled-object-hashes.json').write_text(json.dumps(objects,indent=2)+'\n')
        result['status']='PASS'
    except Exception as e:
        result['status']='FAIL';result['failure']=repr(e);raise
    finally:
        result['finished_at_utc']=now();save()
    print(json.dumps({k:result[k] for k in ['status','local_module_count','audited_declarations','finished_at_utc']},indent=2))
if __name__=='__main__':main()
