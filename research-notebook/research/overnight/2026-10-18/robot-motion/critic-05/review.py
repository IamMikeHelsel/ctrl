from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BUILDER=HERE.parent/'builder-05'
BASE=WORK/'lean-controls'
FRESH=HERE/'.cache/review'
LOG=HERE/'logs'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def main():
    assert not FRESH.exists()
    FRESH.mkdir(parents=True);LOG.mkdir(exist_ok=True)
    result={'started_utc':now(),'status':'RUNNING','builds':[],'kernels':[]}
    def save():(HERE/'review-result.json').write_text(json.dumps(result,indent=2)+'\n')
    manifest=BUILDER/'artifact-sha256.json'
    assert sha(manifest)=='13cd6d9eeaff3f0d930e5cc06adb0541a198162479396a11de4e45ade4c62e50'
    files=json.loads(manifest.read_text())['files']
    for name,v in files.items():assert sha(BUILDER/name)==v['sha256'],name
    result['builder_manifest_files']=len(files);result['builder_manifest_sha256']=sha(manifest)
    bindings=json.loads((BUILDER/'input-bindings.json').read_text())
    for group in ['closure_manifests','toolchain_files']:
        for name,digest in bindings[group].items():assert sha(WORK/name)==digest,name
    closure=json.loads((BUILDER/'source-closure.json').read_text())
    for m,item in closure.items():assert sha(WORK/item['path'])==item['sha256'],m
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=str(WORK/'.tools/elan/bin/lake')
    lean=subprocess.check_output([lake,'env','which','lean'],env=env,cwd=BASE,text=True).strip()
    paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],env=env,cwd=BASE,text=True).strip().split(':')
    paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in paths]
    paths=[p for p in paths if Path(p).resolve()!=(BASE/'.lake/build/lib/lean').resolve()]
    assert all('/.lake/packages/' in p or '/.tools/elan/toolchains/' in p for p in paths),paths
    env['LEAN_PATH']=':'.join([str(FRESH)]+paths)
    env['PATH']=str(Path(lean).parent)+':'+env['PATH']
    checker=Path(lean).parent/'leanchecker'
    envrec={'lean':lean,'checker':str(checker),'lean_sha256':sha(Path(lean)),'checker_sha256':sha(checker),'LEAN_PATH':env['LEAN_PATH'],'ELAN_HOME':env['ELAN_HOME'],'PATH':env['PATH'],'fresh_root':str(FRESH),'public_paths':paths}
    (HERE/'environment.json').write_text(json.dumps(envrec,indent=2)+'\n')
    def run(argv,name):
        start=time.monotonic();r=subprocess.run(argv,cwd=FRESH,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (LOG/(name+'.log')).write_text(r.stdout)
        if r.returncode:raise RuntimeError(name+': '+r.stdout[-3000:])
        return {'exit_code':r.returncode,'log':'logs/'+name+'.log','seconds':time.monotonic()-start}
    try:
        owned=set(closure)
        completed=set()
        for m,item in closure.items():
            p=WORK/item['path'];s=p.read_text()
            imports=re.findall(r'^(?:public )?import\s+(\S+)',s,re.M)
            assert all(dep in completed or dep not in owned for dep in imports),(m,imports)
            code=re.sub(r'--[^\n]*','',s)
            while '/-' in code:
                newer=re.sub(r'/-((?!/-|-/)[\s\S])*?-/', '', code);assert newer!=code;code=newer
            assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',code),m
            dst=FRESH/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
            print('BUILD',m,flush=True)
            result['builds'].append({'module':m,**run([lean,'--root='+str(FRESH),'-o',str(dst.with_suffix('.olean')),str(dst)],'build-'+m)})
            completed.add(m);save()
        audit='''import FutureCommitFixtures
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let owned : Array Name := #[OWNED]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if owned.contains env.allImportedModuleNames[idx.toNat]! then
        if info.isUnsafe then throwError "unsafe local declaration {n}"
        if info.isAxiom then throwError "local axiom {n}"
        let used ← collectAxioms n
        for ax in used do
          unless allowed.contains ax do throwError "unapproved axiom {ax} in {n}"
        logInfo m!"DECL|{n}|{used}"
'''.replace('OWNED',','.join('`'+m for m in closure))
        (HERE/'ReviewAudit.lean').write_text(audit);(FRESH/'ReviewAudit.lean').write_text(audit)
        result['audit']=run([lean,'--root='+str(FRESH),str(FRESH/'ReviewAudit.lean')],'audit')
        result['local_declarations']=(LOG/'audit.log').read_text().count('DECL|')
        for m in closure:
            print('KERNEL',m,flush=True)
            result['kernels'].append({'module':m,**run([str(checker),m,'-v'],'kernel-'+m)});save()
        for name,v in files.items():assert sha(BUILDER/name)==v['sha256'],name
        result['status']='PASS'
    except Exception as e:result['status']='FAIL';result['error']=repr(e);raise
    finally:result['finished_utc']=now();save()
if __name__=='__main__':main()
