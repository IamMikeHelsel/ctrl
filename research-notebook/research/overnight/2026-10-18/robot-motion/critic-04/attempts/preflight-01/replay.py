"""Independent fresh closure rebuild and strict falsification controls."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, time
import oracle

HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BUILDER=HERE.parent/'builder-04'
BASE=WORK/'lean-controls'
CACHE=HERE/'.cache/fresh'
LOGS=HERE/'logs'
MANIFEST_SHA='025661f2f14bd9bdb3ef12ba49bdbd73d364c41971da1e749c50073a07e46023'
FREEZE_SHA='c55250cfe0744adcdc30e4ea9434b41c1052b1ba4cd2dd49271fb89a15be0eae'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()

def main():
    assert not CACHE.exists(), 'Use a fresh sibling directory for a new replay'
    CACHE.mkdir(parents=True);LOGS.mkdir()
    result={'status':'RUNNING','started_utc':now(),'builder_manifest_sha256':MANIFEST_SHA,
            'source_freeze_sha256':FREEZE_SHA,'commands':[]}
    def save(): (HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=WORK/'.tools/elan/bin/lake'
    def query(*args):
        return subprocess.check_output([str(lake),'env',*args],cwd=BASE,env=env,text=True).strip()
    lean=query('which','lean'); checker=str(Path(lean).parent/'leanchecker')
    deps=[]
    for entry in query('printenv','LEAN_PATH').split(':'):
        p=(BASE/entry).resolve()
        if p==(BASE/'.lake/build/lib/lean').resolve():continue
        assert '.lake/packages/' in str(p), f'unexpected dependency path {p}'
        deps.append(str(p))
    env['LEAN_PATH']=':'.join([str(CACHE),*deps])
    env['PATH']=str(Path(lean).parent)+':'+env['PATH']
    result['environment']={'LEAN_PATH':env['LEAN_PATH'],'lean_version':subprocess.check_output([lean,'--version'],text=True).strip(),
                           'lean_sha256':sha(Path(lean)),'leanchecker_sha256':sha(Path(checker))}
    assert '4.35.0' in result['environment']['lean_version']
    closure=json.loads((BUILDER/'source-closure.json').read_text())
    pins=json.loads((BUILDER/'input-bindings.json').read_text())
    artifact=json.loads((BUILDER/'artifact-sha256-final.json').read_text())
    def preserved():
        assert sha(BUILDER/'artifact-sha256-final.json')==MANIFEST_SHA
        assert sha(BUILDER/'source-freeze.json')==FREEZE_SHA
        for name,v in artifact['files'].items(): assert sha(BUILDER/name)==v['sha256'],name
        for name,v in closure.items(): assert sha(WORK/v['path'])==v['sha256'],name
        for group in ['closure_manifests','toolchain_files']:
            for name,digest in pins[group].items(): assert sha(WORK/name)==digest,name
        for name,v in pins['sources'].items(): assert sha(WORK/v['path'])==v['sha256'],name
        return {'artifact_files':len(artifact['files']),'source_modules':len(closure),'pins':len(pins['toolchain_files'])}
    def run(args,label,negative=False):
        start=time.monotonic();p=subprocess.run(args,cwd=CACHE,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log=LOGS/(label+'.log');log.write_text(p.stdout)
        r={'label':label,'command':args,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,5),'log':str(log.relative_to(HERE)),'log_sha256':sha(log)}
        result['commands'].append(r);save()
        if negative:
            assert p.returncode!=0 and re.search(r'⊢\s*False',p.stdout), p.stdout
            assert not any(s in p.stdout for s in ['unknown identifier','unknown constant','unknown module prefix','object file','made no progress','unsolved synthetic']),p.stdout
        else:
            assert p.returncode==0,p.stdout[-12000:]
        return r
    def compile_module(name,path):
        dst=CACHE/(name.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,dst)
        print('BUILD',name,flush=True)
        run([lean,'--root='+str(CACHE),'-o',str(dst.with_suffix('.olean')),str(dst)],'build-'+name)
    try:
        result['preservation_before']=preserved();save()
        # Establish a new topological order from actual imports, not the builder's order.
        order=[]; visiting=set()
        def visit(name):
            if name in order:return
            assert name not in visiting,'cycle';visiting.add(name)
            path=WORK/closure[name]['path']
            imports=re.findall(r'^(?:public\s+)?import\s+([^\n]+)',path.read_text(),re.M)
            for line in imports:
                for dep in line.split('--')[0].split():
                    if dep in closure:visit(dep)
                    else: assert dep.startswith(('Mathlib','Lean','Std','Init')),dep
            visiting.remove(name);order.append(name)
        for name in closure:visit(name)
        result['module_order']=order
        for name in order:compile_module(name,WORK/closure[name]['path'])
        result['oracle']={k:v for k,v in oracle.generate().items() if k!='cases'};save()
        compile_module('ReviewerOracle',HERE/'ReviewerOracle.lean')
        compile_module('ReviewerWitnesses',HERE/'ReviewerWitnesses.lean')
        owned=order+['ReviewerOracle','ReviewerWitnesses']
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
        (HERE/'EnvironmentAudit.lean').write_text(audit);(CACHE/'EnvironmentAudit.lean').write_text(audit)
        run([lean,'--root='+str(CACHE),str(CACHE/'EnvironmentAudit.lean')],'axiom-audit')
        result['audited_declarations']=(LOGS/'axiom-audit.log').read_text().count('DECL|')
        result['builder_local_declarations']=sum(1 for line in (LOGS/'axiom-audit.log').read_text().splitlines() if line.startswith('DECL|') and line.split('|')[1] in order)
        for name in owned:
            print('KERNEL',name,flush=True);run([checker,name,'-v'],'kernel-'+name)
        for path in sorted((HERE/'negative-controls').glob('*.lean')):
            dst=CACHE/path.name;shutil.copyfile(path,dst)
            run([lean,'--root='+str(CACHE),str(dst)],'negative-'+path.stem,negative=True)
        result['preservation_after']=preserved()
        result['status']='PASS'
    except Exception as e:
        result['status']='FAIL';result['error']=repr(e);raise
    finally:
        result['finished_utc']=now();save()
    print(json.dumps({k:v for k,v in result.items() if k not in ['commands','environment']},indent=2))

if __name__=='__main__': main()
