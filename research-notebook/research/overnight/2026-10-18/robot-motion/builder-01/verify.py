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
    env['LEAN_PATH']=str(ROOT)+':'+deps
    env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    sources=dev.source_closure('TimedAdmission')
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
            assert p.returncode!=0 and 'error:' in p.stdout and 'False' in p.stdout
            assert not any(x in p.stdout for x in ['unknown identifier','unknown constant','object file','unknown module prefix'])
        elif p.returncode:
            print(p.stdout[-12000:],flush=True);raise RuntimeError(name)
        return {'command':args,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,6),
          'log':str(log.relative_to(HERE)),'log_sha256':sha(log)}
    try:
        for m,p in sources.items():
            assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',code(p.read_text())),m
            dst=ROOT/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
            print('BUILD',m,flush=True)
            result['builds'].append({'module':m,**run([lean,'--root='+str(ROOT),'-o',str(dst.with_suffix('.olean')),str(dst)],'build-'+m.replace('.','_'))});save()
        audit='''import TimedAdmission
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
        for m in ['Kernel','RationalGuard','Reference','AccelerationGuard','AccelerationFixtures','ReversalProposal','TimedAdmission']:
            print('KERNEL',m,flush=True)
            result['kernel'].append({'module':m,**run([str(checker),m,'-v'],'kernel-'+m)});save()
        negatives={
          'FalseAccelAcceptance':'''import TimedAdmission
open RobotMotion RobotMotion.AccelerationAdmission
example : checkAcceleration (1/5) (1/2) 0 returnGenerous = true := by
  rw [new_acceleration_guard_rejects]
  norm_num
''',
          'FalseInteriorBound':'''import TimedAdmission
open RobotMotion RobotMotion.AccelerationAdmission
example : qAcceleration 1 [(0,1)] (4/3) ≤ 1/2 := by
  rw [off_knot_peak]
  norm_num
''',
          'FalseDeadlineSelection':'''import TimedAdmission
open RobotMotion RobotMotion.AccelerationAdmission
example : chooseExecution (1/5) (1/2) (15/2) (13/25) (13/10)
    [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := by
  rw [insufficient_candidate_deadline]
  norm_num
''',
          'FalsePastAdmission':'''import TimedAdmission
open RobotMotion RobotMotion.AccelerationAdmission
example : checkTimedCandidate (1/5) (1/2) (15/2) (7/10) (17/10)
    [(11/50,1/50)] (-1/50) (31/50) = true := by
  rw [past_candidate_rejected]
  norm_num
'''}
        nd=HERE/'negative-controls';nd.mkdir(exist_ok=True)
        for name,text in negatives.items():
            (nd/(name+'.lean')).write_text(text);dst=ROOT/(name+'.lean');dst.write_text(text)
            result['negative_controls'].append({'name':name,**run([lean,'--root='+str(ROOT),str(dst)],'negative-'+name,True)})
        assert all(sha(p)==before[m]['sha256'] for m,p in sources.items())
        freeze=json.loads((HERE/'source-freeze.json').read_text())
        assert all(sha(HERE/n)==v['sha256'] for n,v in freeze['files'].items())
        assert sha(dev.BASE/'lake-manifest.json')==result['lake_manifest_sha256']
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
