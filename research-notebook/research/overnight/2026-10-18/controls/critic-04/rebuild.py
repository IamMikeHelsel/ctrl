#!/usr/bin/env python3
"""Independent reviewer replay. No builder implementation code is imported."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time,sys
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BUILDER=HERE.parent/'builder-04'
BASE=WORK/'lean-controls'
EXPECTED='fcd32812a407ff8589951ef313da896c106751fef00fa987cfefe4ae64327a9b'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(): (HERE/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args,cwd=None,negative=False):
    p=HERE/'logs'/(label+'.log'); start=time.monotonic()
    with p.open('w') as out: result=subprocess.run(args,cwd=cwd or BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
    ok=result.returncode!=0 if negative else result.returncode==0
    if negative:
        s=p.read_text(); ok=ok and 'unsolved goals' in s and 'unknown' not in s and 'failed to synthesize' not in s
    report['steps'].append({'label':label,'exit':result.returncode,'pass':ok,'seconds':time.monotonic()-start,'log_sha256':sha(p)})
    save();print(label,result.returncode,flush=True);assert ok,label
manifest=BUILDER/'artifact-sha256.json';assert sha(manifest)==EXPECTED
frozen=json.loads(manifest.read_text())['files']
assert all(sha(BUILDER/p)==h for p,h in frozen.items())
closure=json.loads((BUILDER/'source-closure.json').read_text())
assert len(closure)==43
assert all(sha(WORK/x['path'])==x['sha256'] for x in closure.values())
freeze=json.loads((BUILDER/'source-freeze.json').read_text())['files']
assert all(freeze[x['path']]['sha256']==x['sha256'] for x in closure.values())
# Independently validate dependency reachability and order.
def imports(p):
    s=re.sub(r'/-.*?-/','',p.read_text(),flags=re.S)
    out=[]
    for line in s.splitlines():
        m=re.match(r'\s*(?:public\s+)?import\s+(.+?)(?:--.*)?$',line)
        if m:out.extend(m.group(1).split())
    return out
order=[]; visiting=set();done=set()
def visit(m):
    if m in done:return
    assert m not in visiting
    visiting.add(m)
    for d in imports(WORK/closure[m]['path']):
        if d in closure:visit(d)
        else:assert d.startswith(('Mathlib.','Lean.','Std.')),(m,d)
    visiting.remove(m);done.add(m);order.append(m)
visit('QuadraticWitness'); assert set(order)==set(closure)
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=WORK/'.tools/elan/bin/lake'
def query(*args):return subprocess.check_output([str(lake),'env',*args],cwd=BASE,env=env,text=True).strip()
lean=Path(query('which','lean')); checker=lean.with_name('leanchecker')
deps=[]
for s in query('printenv','LEAN_PATH').split(':'):
    p=(BASE/s).resolve() if not Path(s).is_absolute() else Path(s)
    if '/.lake/packages/' in str(p):deps.append(str(p))
assert deps
BUILD=HERE/'fresh';BUILD.mkdir(exist_ok=False);(HERE/'logs').mkdir(exist_ok=True)
env['LEAN_PATH']=str(BUILD)+':'+':'.join(deps)
env['PATH']=str(lean.parent)+':'+env.get('PATH','')
version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip()
assert '4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version
mathlib=BASE/'.lake/packages/mathlib'
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()
status=subprocess.check_output(['git','status','--porcelain'],cwd=mathlib,text=True)
assert rev=='56a005855ea17e0b0958f73ec801ae140b0a1679' and not status
report={'passed':False,'builder_manifest_sha256':EXPECTED,'builder_files_before':len(frozen),'source_count':len(closure),'closure':closure,'order':order,'lean':version,'mathlib':rev,'mathlib_status':status,'dependency_paths':deps,'steps':[]}
save()
for m in order:
    src=WORK/closure[m]['path'];dest=BUILD/(m.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
    assert sha(dest)==closure[m]['sha256']
    run('build-'+m,[str(lean),'--root='+str(BUILD),'-o',str(dest.with_suffix('.olean')),str(dest)])
audit='''import QuadraticWitness
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
'''.replace('OWNED',', '.join('`'+x for x in order))
(BUILD/'Audit.lean').write_text(audit);(HERE/'Audit.lean').write_text(audit)
run('all-local-declaration-audit',[str(lean),str(BUILD/'Audit.lean')])
records=[x for x in (HERE/'logs/all-local-declaration-audit.log').read_text().splitlines() if x.startswith('DECL|')]
report['audited_declarations']=len(records);save();assert len(records)>628
for m in ['ComparisonEnvelope','RobustHold','ScaledTracking','Settling','SettlingFixtures','FrozenReference','DirectReference','QuadraticAlgebra','QuadraticTrajectory','QuadraticWitness']:
    run('kernel-'+m,[str(checker),m,'-v'])
report['builder_files_unchanged']=all(sha(BUILDER/p)==h for p,h in frozen.items())
report['sources_unchanged']=all(sha(WORK/x['path'])==x['sha256'] for x in closure.values())
report['passed']=report['builder_files_unchanged'] and report['sources_unchanged'] and all(x['pass'] for x in report['steps']);save();print(json.dumps({k:report[k] for k in ['passed','source_count','audited_declarations']}))
(HERE/'environment.json').write_text(json.dumps({'lean':str(lean),'checker':str(checker),'env':{k:env[k] for k in ['ELAN_HOME','LEAN_PATH','PATH']},'build':str(BUILD)},indent=2)+'\n')
