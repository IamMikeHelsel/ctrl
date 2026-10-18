"""Continue after reviewer-only client normalization repair; preserve first run."""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time
import replay

H=replay.HERE; C=replay.CACHE; B=replay.BUILDER; W=replay.WORK
sha=replay.sha
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def main():
    first=json.loads((H/'result.json').read_text())
    assert first['status']=='FAIL'
    assert first['commands'][-1]['label']=='build-ReviewerWitnesses'
    assert all(x['exit_code']==0 for x in first['commands'][:-1])
    assert len(first['commands'])==17
    logs=H/'final-logs';logs.mkdir()
    env=os.environ.copy();env['ELAN_HOME']=str(W/'.tools/elan');env['LEAN_PATH']=first['environment']['LEAN_PATH']
    lean=first['commands'][0]['command'][0]; checker=str(Path(lean).parent/'leanchecker')
    env['PATH']=str(Path(lean).parent)+':'+env['PATH']
    closure=json.loads((B/'source-closure.json').read_text());owned=list(closure)+['ReviewerOracle','ReviewerWitnesses']
    result={'status':'RUNNING','started_utc':now(),'first_run_sha256':sha(H/'result.json'),
            'repair':'Three reviewer client negation normalizations only; first 15-module fresh build and oracle are unchanged.',
            'fresh_successful_modules_before_repair':first['module_order']+['ReviewerOracle'],'commands':[]}
    def save():(H/'final-result.json').write_text(json.dumps(result,indent=2)+'\n')
    def preserved():
        assert sha(B/'artifact-sha256-final.json')==replay.MANIFEST_SHA
        assert sha(B/'source-freeze.json')==replay.FREEZE_SHA
        counts={}
        for manifest in ['artifact-sha256.json','artifact-sha256-final.json','source-freeze.json']:
            fs=json.loads((B/manifest).read_text())['files']
            for name,v in fs.items():assert sha(B/name)==v['sha256']
            counts[manifest]=len(fs)
        for name,v in closure.items():
            assert sha(W/v['path'])==v['sha256']
            assert sha(C/(name+'.lean'))==v['sha256']
        assert sha(C/'ReviewerOracle.lean')==sha(H/'ReviewerOracle.lean')
        pins=json.loads((B/'input-bindings.json').read_text())
        for group in ['closure_manifests','toolchain_files']:
            for name,digest in pins[group].items():assert sha(W/name)==digest
        assert sha(Path(lean))==first['environment']['lean_sha256']
        assert sha(Path(checker))==first['environment']['leanchecker_sha256']
        return counts
    def run(args,label,negative=False):
        start=time.monotonic();p=subprocess.run(args,cwd=C,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log=logs/(label+'.log');log.write_text(p.stdout)
        result['commands'].append({'label':label,'command':args,'exit_code':p.returncode,'seconds':time.monotonic()-start,'log':str(log.relative_to(H)),'log_sha256':sha(log)});save()
        if negative:
            assert p.returncode!=0 and re.search(r'⊢\s*False',p.stdout),p.stdout
            assert not any(s in p.stdout for s in ['unknown identifier','unknown constant','unknown module prefix','object file','made no progress','unsolved synthetic']),p.stdout
        else:assert p.returncode==0,p.stdout[-12000:]
    try:
        result['preservation_before']=preserved();save()
        source=H/'ReviewerWitnesses.lean';dst=C/source.name;shutil.copyfile(source,dst)
        run([lean,'--root='+str(C),'-o',str(dst.with_suffix('.olean')),str(dst)],'build-ReviewerWitnesses')
        audit='''import VelocityOracle
import ReviewerOracle
import ReviewerWitnesses
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
'''.replace('OWNED',','.join('`'+n for n in owned))
        (H/'EnvironmentAudit.lean').write_text(audit);(C/'EnvironmentAudit.lean').write_text(audit)
        run([lean,'--root='+str(C),str(C/'EnvironmentAudit.lean')],'axiom-audit')
        lines=(logs/'axiom-audit.log').read_text().splitlines()
        result['audited_declarations']=sum(line.startswith('DECL|') for line in lines)
        result['builder_local_declarations']=sum(line.startswith('DECL|') and line.split('|')[1] in closure for line in lines)
        for name in owned:
            print('KERNEL',name,flush=True);run([checker,name,'-v'],'kernel-'+name)
        for source in sorted((H/'negative-controls').glob('*.lean')):
            dst=C/source.name;shutil.copyfile(source,dst)
            run([lean,'--root='+str(C),str(dst)],'negative-'+source.stem,True)
        result['preservation_after']=preserved()
        result['objects']={str(p.relative_to(C)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in C.rglob('*') if p.is_file() and p.suffix!='.lean'}
        result['status']='PASS'
    except Exception as e:
        result['status']='FAIL';result['error']=repr(e);raise
    finally:result['finished_utc']=now();save()
    print(json.dumps({k:v for k,v in result.items() if k not in ['commands','objects']},indent=2))
if __name__=='__main__':main()
