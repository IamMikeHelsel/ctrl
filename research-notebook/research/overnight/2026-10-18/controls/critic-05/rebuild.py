#!/usr/bin/env python3
"""Independent source binding, fresh compilation, axiom and kernel review."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, time

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[4]
BUILDER = HERE.parent / 'builder-05'
BASE = WORK / 'lean-controls'
EXPECTED = '4036417f36ccf705244f9b285c8bdf4e98245d325c522a280ed8aeeed9ab2f00'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def verify_manifest(path, expected):
    assert sha(path) == expected, path
    data = json.loads(path.read_text())['files']
    for name, entry in data.items():
        digest = entry if isinstance(entry, str) else entry['sha256']
        assert sha(path.parent/name) == digest, (path, name)
    return len(data)

inputs = {
 'controls/builder-05/artifact-sha256.json': EXPECTED,
 'controls/builder-04/artifact-sha256.json': 'fcd32812a407ff8589951ef313da896c106751fef00fa987cfefe4ae64327a9b',
 'controls/critic-04/artifact-sha256.json': '96dffbd77ad98c637e56716c22c91f76de612b09b7e87063e08dda584c169773',
 'robot-motion/builder-02/artifact-sha256.json': '3abb293d650c12e90e1f36dc6296b0b81a2dbbe570692ed4ffdaaaa9f0dacf20',
 'robot-motion/critic-02/artifact-sha256.json': 'fbc7ba5ddeb97c92b788f670fa8c483708366c0c2bfdb7da246128d064df9470',
}
bound = {p:{'sha256':h,'files':verify_manifest(HERE.parents[1]/p,h)} for p,h in inputs.items()}
closure = json.loads((BUILDER/'source-closure.json').read_text())
assert len(closure) == 54
for name, entry in closure.items():
    assert sha(WORK/entry['path']) == entry['sha256']
    assert (WORK/entry['path']).is_relative_to(BUILDER)
def imports(path):
    text = re.sub(r'/-.*?-/','',path.read_text(),flags=re.S)
    result=[]
    for line in text.splitlines():
        m=re.match(r'\s*(?:public\s+)?import\s+(.+?)(?:--.*)?$',line)
        if m: result.extend(m.group(1).split())
    return result
order=[]; seen=set(); active=set()
def visit(name):
    if name in seen: return
    assert name not in active
    active.add(name)
    for dep in imports(WORK/closure[name]['path']):
        if dep in closure: visit(dep)
        else: assert dep.startswith(('Mathlib.','Lean.','Std.')), (name,dep)
    active.remove(name); seen.add(name); order.append(name)
visit('FIRHoldWitness')
assert set(order)==set(closure)
env=os.environ.copy(); env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=WORK/'.tools/elan/bin/lake'
def query(*args): return subprocess.check_output([str(lake),'env',*args],cwd=BASE,env=env,text=True).strip()
lean=Path(query('which','lean')); checker=lean.with_name('leanchecker')
deps=[]
for entry in query('printenv','LEAN_PATH').split(':'):
    p=(BASE/entry).resolve() if not Path(entry).is_absolute() else Path(entry)
    if '/.lake/packages/' in str(p): deps.append(str(p))
assert deps
BUILD=HERE/'fresh'; BUILD.mkdir(exist_ok=False)
(HERE/'logs').mkdir(exist_ok=True)
env['LEAN_PATH']=str(BUILD)+':'+':'.join(deps)
env['PATH']=str(lean.parent)+':'+env.get('PATH','')
version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip()
assert '4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version
mathlib=BASE/'.lake/packages/mathlib'
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()
status=subprocess.check_output(['git','status','--porcelain'],cwd=mathlib,text=True)
assert rev=='56a005855ea17e0b0958f73ec801ae140b0a1679' and not status
assert sha(BASE/'lake-manifest.json')=='6525e7195148f78782a5aeeee8f1a8a90eebc4ecd4e9c3cdc215b29ddd3fbcb0'
report={'passed':False,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'input_manifests':bound,'closure':closure,'order':order,'toolchain':version,
 'mathlib':rev,'mathlib_status':status,'dependency_paths':deps,'steps':[]}
def save(): (HERE/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label, args):
    path=HERE/'logs'/(label+'.log'); start=time.monotonic()
    with path.open('w') as log:
        proc=subprocess.run(args,cwd=BUILD,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
    report['steps'].append({'label':label,'exit':proc.returncode,'seconds':time.monotonic()-start,'log_sha256':sha(path)})
    save(); print(label,proc.returncode,flush=True); assert proc.returncode==0,label
save()
(HERE/'environment.json').write_text(json.dumps({'lean':str(lean),'checker':str(checker),'env':{k:env[k] for k in ['ELAN_HOME','LEAN_PATH','PATH']},'build':str(BUILD)},indent=2)+'\n')
for name in order:
    dest=BUILD/(name.replace('.','/')+'.lean'); dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(WORK/closure[name]['path'],dest); assert sha(dest)==closure[name]['sha256']
    run('build-'+name,[str(lean),'--root='+str(BUILD),'-o',str(dest.with_suffix('.olean')),str(dest)])
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
        if info.isUnsafe then throwError m!"UNSAFE|{mod}|{n}"
        if info.isAxiom then throwError m!"AXIOM|{mod}|{n}"
        let used ← collectAxioms n
        for ax in used do
          unless allowed.contains ax do throwError m!"BADAX|{mod}|{n}|{ax}"
        logInfo m!"DECL|{mod}|{n}|{info.isTheorem}|{used}"
'''.replace('OWNED',', '.join('`'+m for m in order))
(HERE/'Audit.lean').write_text(audit); (BUILD/'Audit.lean').write_text(audit)
run('all-local-declaration-audit',[str(lean),str(BUILD/'Audit.lean')])
rows=[x for x in (HERE/'logs/all-local-declaration-audit.log').read_text().splitlines() if x.startswith('DECL|')]
report['audited_declarations']=len(rows)
assert {x.split('|')[1] for x in rows}==set(order)
assert len(rows)==3184
targets=['ComparisonEnvelope','RobustHold','ScaledTracking','Composition','PhysicalArrival','Settling','SettlingFixtures','QuadraticAlgebra','QuadraticTrajectory','FIRHold','FIRHoldWitness']
for name in targets: run('kernel-'+name,[str(checker),name,'-v'])
report['kernel_targets']=targets
report['input_manifests_after']={p:verify_manifest(HERE.parents[1]/p,h) for p,h in inputs.items()}
report['sources_unchanged']=all(sha(WORK/x['path'])==x['sha256'] for x in closure.values())
report['passed']=report['sources_unchanged']
report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
save(); print(json.dumps({'passed':report['passed'],'fresh_modules':len(order),'audited_declarations':len(rows),'kernel_modules':len(targets)}))
