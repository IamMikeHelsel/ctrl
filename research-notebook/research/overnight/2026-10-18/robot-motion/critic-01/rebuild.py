"""Independent frozen-source closure rebuild. Does not invoke builder scripts."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, time

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[4]
BUILDER = HERE.parent / 'builder-01'
BASE = WORK / 'lean-controls'
FRESH = HERE / '.cache/fresh'
LOGS = HERE / 'logs'
PRIOR = WORK / 'research/pods/2026-10-17/robot-motion/certificate-03/builder'
NEW = ['AccelerationGuard','AccelerationFixtures','ReversalProposal','TimedAdmission']
PATHS = {p.stem:p for p in PRIOR.glob('*.lean')}
PATHS.update({m:BUILDER/(m+'.lean') for m in NEW})

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(): (HERE/'rebuild.json').write_text(json.dumps(result, indent=2)+'\n')
def clean(s):
    while '/-' in s:
        t=re.sub(r'/-((?!/-|-/)[\s\S])*?-/', '', s)
        assert t!=s
        s=t
    return re.sub(r'--[^\n]*','',s)

result={'status':'RUNNING','started_at_utc':now(),'builds':[], 'replays':[]}
assert not FRESH.exists(), 'Fresh build only'
FRESH.mkdir(parents=True)
LOGS.mkdir(exist_ok=True)
manifest=BUILDER/'artifact-sha256.json'
freeze=BUILDER/'source-freeze.json'
assert sha(manifest)=='26834db326ef426ab5bb136d8b8ccf660fc10df857bc2203e3291ee511b05bfc'
assert sha(freeze)=='23f1e686988f7509588a597aeaaa70559f36eb8fbc47bac7b2ef5b80870ada92'
for p,v in json.loads(manifest.read_text())['files'].items():
    assert sha(BUILDER/p)==v['sha256'], p
result['builder_manifest_sha256']=sha(manifest)
result['source_freeze_sha256']=sha(freeze)
result['builder_artifact_files_checked']=len(json.loads(manifest.read_text())['files'])
for p,v in json.loads((BUILDER/'prior-evidence.json').read_text())['files'].items():
    assert sha(WORK/p)==v['sha256'], p
result['prior_evidence_files_checked']=len(json.loads((BUILDER/'prior-evidence.json').read_text())['files'])
env=os.environ.copy(); env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args): return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=query('which','lean'); checker=str(Path(lean).parent/'leanchecker')
deps=':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':'))
env['LEAN_PATH']=str(FRESH)+':'+deps
env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
result['lean_toolchain']=(BASE/'lean-toolchain').read_text().strip()
result['manifest_sha256']=sha(BASE/'lake-manifest.json')
result['lean_sha256']=sha(Path(lean));result['checker_sha256']=sha(Path(checker))
result['lean_path']=env['LEAN_PATH']
closure={}
def visit(m):
    if m in closure:return
    p=PATHS.get(m)
    if p is None:
        assert m.startswith(('Mathlib.','Lean.')), m
        return
    code=clean(p.read_text())
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',code),m
    for dep in re.findall(r'^(?:public )?import (\S+)',code,re.M): visit(dep)
    closure[m]=p
visit('TimedAdmission')
result['source_closure']={m:{'path':str(p.relative_to(WORK)),'sha256':sha(p)} for m,p in closure.items()}
def run(args,name):
    start=time.monotonic()
    p=subprocess.run(args,cwd=FRESH,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=LOGS/(name+'.log');log.write_text(p.stdout)
    rec={'exit_code':p.returncode,'seconds':time.monotonic()-start,'log':str(log.relative_to(HERE)),'log_sha256':sha(log),'command':args}
    assert p.returncode==0, (name,p.stdout[-12000:])
    return rec
try:
    for m,p in closure.items():
        dst=FRESH/(m+'.lean');shutil.copyfile(p,dst)
        print('BUILD',m,flush=True)
        result['builds'].append({'module':m,**run([lean,'--root='+str(FRESH),'-o',str(dst.with_suffix('.olean')),str(dst)],'build-'+m)});save()
    audit='''import TimedAdmission
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let localModules : Array Name := #[MODULES]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.allImportedModuleNames[idx.toNat]!
      if localModules.contains moduleName then
        if info.isUnsafe then throwError "UNSAFE {name}"
        if info.isAxiom then throwError "LOCAL_AXIOM {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "UNAPPROVED {name} {ax}"
        logInfo m!"AUDIT|{moduleName}|{name}|theorem={info.isTheorem}|{axioms}"
'''.replace('MODULES',','.join('`'+m for m in closure))
    (HERE/'IndependentAudit.lean').write_text(audit)
    result['axiom_audit']=run([lean,'--root='+str(FRESH),str(HERE/'IndependentAudit.lean')],'axiom-audit')
    result['audited_declarations']=(LOGS/'axiom-audit.log').read_text().count('AUDIT|')
    for m in closure:
        print('REPLAY',m,flush=True)
        result['replays'].append({'module':m,**run([checker,m,'-v'],'kernel-'+m)});save()
    assert all(sha(p)==result['source_closure'][m]['sha256'] for m,p in closure.items())
    assert sha(BASE/'lake-manifest.json')==result['manifest_sha256']
    assert sha(manifest)==result['builder_manifest_sha256']
    result['compiled_objects']={str(p.relative_to(FRESH)):sha(p) for p in FRESH.glob('*.olean*')}
    result['status']='PASS'
except Exception as exc:
    result['status']='FAIL';result['error']=repr(exc);raise
finally:
    result['finished_at_utc']=now();save()
