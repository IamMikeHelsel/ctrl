"""Independent fresh source review. Writes only to critic-03."""
from pathlib import Path
import os, subprocess, hashlib, json, re, time
B=Path(__file__).resolve().parent;A=B.parent/'builder-03';R=B.parents[4];L=R/'lean-controls';T=B/'cache'
mods=['CliffordModel','HyperbolicSpinor','SpinorDimensions','SplitSpinor','FockOperators','VacuumProjector','FockImage','WordActions','MatrixUnits','FullImage','RealEquivalence','OrderControls','BasisActions','TransposeBridge','VolumeForm','RealAdjoint','AdjointControls']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'builder-03':'3a6f59f0b26b0b60541fbb7d913be8dfb5c61ee0d7e8b9e10f8c36a1ae3ccf24','builder-02':'fab7240941cb89b4517fd2614160f7ebf122eff095b017f4676bd09cd94b792d','critic-02':'7984208c7cd519eb42eceb8264d6047af00c0d5869548d1ad17e57fcf4895c73','analyst-01':'0c667224d83d64fc6cd9b764e1a556da23e5c7f90ef462b5f5f35149e60f579e','critic-01':'d525512033db6160c60ee77cc032a68e103253fa6604c620deb79077d4e640d3'}
def frozen():
 out={}
 for f,h in pins.items():
  d=B.parent/f;m=d/'SHA256SUMS';assert sha(m)==h,(f,'manifest')
  lines=m.read_text().splitlines()
  for line in lines:
   expected,p=line.split('  ',1);assert sha(d/p)==expected,(f,p)
  out[f]={'manifest_sha256':h,'files':len(lines)}
 for m in mods[:13]:assert sha(A/(m+'.lean'))==sha(B.parent/'builder-02'/(m+'.lean'))
 return out
before=frozen()
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=L,env=env,text=True).strip()
version=subprocess.check_output([lean,'--version'],env=env,text=True).strip();assert '4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version
manifest=json.loads((L/'lake-manifest.json').read_text());mathlib=next(x for x in manifest['packages'] if x['name']=='mathlib')['rev'];assert mathlib=='56a005855ea17e0b0958f73ec801ae140b0a1679'
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=L,env=env,text=True).strip().split(':')
deps=[str((L/p).resolve()) for p in paths if (L/p).resolve()!=(L/'.lake/build/lib/lean').resolve()]
assert all('/.lake/packages/' in p or Path(p) == Path(lean).parent.parent/'lib/lean' for p in deps),deps
assert not list(T.glob('*.olean')),'fresh output directory required'
env['LEAN_PATH']=str(T)+':'+':'.join(deps);env['PATH']=str(Path(lean).parent)+':'+env['PATH']
(B/'environment.json').write_text(json.dumps({'lean':version,'mathlib':mathlib,'lean_path':env['LEAN_PATH'],'project_cache_excluded':True},indent=2)+'\n')
steps=[]
def run(name,cmd,negative=False):
 start=time.monotonic();p=subprocess.run(cmd,cwd=T,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
 (B/'logs'/(name+'.txt')).write_text(p.stdout)
 steps.append(dict(name=name,returncode=p.returncode,seconds=round(time.monotonic()-start,3),command=cmd))
 (B/'run-progress.json').write_text(json.dumps(steps,indent=2)+'\n');print(name,p.returncode,flush=True)
 assert (p.returncode!=0 if negative else p.returncode==0),p.stdout
 if negative:
  assert 'unsolved goals' in p.stdout or 'type mismatch' in p.stdout.lower(),p.stdout
  assert not any(x in p.stdout.lower() for x in ['unknown identifier','unknown module','file not found','failed to synthesize'])
 return p.stdout
for m in mods:
 source=(A/(m+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source)
 (T/(m+'.lean')).write_bytes((A/(m+'.lean')).read_bytes())
 run('build-'+m,[lean,'--root='+str(T),'-o',str(T/(m+'.olean')),str(T/(m+'.lean'))])
(T/'ReviewClient.lean').write_bytes((B/'ReviewClient.lean.txt').read_bytes())
run('ReviewClient',[lean,'--root='+str(T),'-o',str(T/'ReviewClient.olean'),str(T/'ReviewClient.lean')])
audit='''import ReviewClient
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
 let env ← getEnv
 let owned : Array Name := #[OWNED]
 let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
 for (n,info) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   let mod := env.allImportedModuleNames[idx.toNat]!
   if owned.contains mod then
    if info.isUnsafe then throwError "unsafe local declaration: {n}"
    if info.isAxiom then throwError "local axiom: {n}"
    let axs ← collectAxioms n
    for ax in axs do
     unless allowed.contains ax do throwError "unexpected axiom: {n}: {ax}"
    logInfo m!"DECL|{mod}|{n}|{info.isTheorem}|{axs}"
'''.replace('OWNED',', '.join('`'+m for m in mods+['ReviewClient']))
(B/'Audit.lean.txt').write_text(audit);(T/'Audit.lean').write_text(audit)
aout=run('axioms',[lean,str(T/'Audit.lean')]);rows=[x for x in aout.splitlines() if x.startswith('DECL|')];assert rows
negative={
 'WrongTranspose':'example : (positiveMatrix 0).transpose = -positiveMatrix 0 := by\n  rw [positive_transpose]\n',
 'OneSided':'example : K * (positiveMatrix 0).transpose = -positiveMatrix 0 := by\n  rw [positive_transpose]\n',
 'KNegativeSquare':'example : K*K = -1 := by\n  rw [K_square]\n',
 'ReverseUnchanged':'example : negativeMatrix 6 * negativeMatrix 5 * negativeMatrix 4 * negativeMatrix 3 * negativeMatrix 2 * negativeMatrix 1 * negativeMatrix 0 = K := by\n  rw [reversed_negative_product]\n',
 'VectorFixed':'example : splitMatrixEquiv (star (gamma 0)) = positiveMatrix 0 := by\n  change splitMatrix (star (gamma 0)) = positiveMatrix 0\n  rw [splitMatrix_star]\n  change realAdjoint (positiveMatrix 0) = positiveMatrix 0\n  rw [realAdjoint_positive]\n',
 'ComplexPlainTranspose':'example : ((Complex.I : ℂ) • (1 : ComplexSpinMatrix)).transpose = -(Complex.I • (1 : ComplexSpinMatrix)) := by\n  ext I J\n  simp [Matrix.transpose_apply, Matrix.one_apply]\n'}
for n,s in negative.items():
 src='import ReviewClient\nnoncomputable section\nopen HyperbolicSpinor GUClifford\n'+s
 (B/(n+'.lean.txt')).write_text(src);(T/(n+'.lean')).write_text(src)
 run(n,[lean,str(T/(n+'.lean'))],True)
for m in mods+['ReviewClient']:run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'])
assert frozen()==before
result={'status':'PASS','fresh_modules':len(mods),'reviewer_theorems':len(re.findall(r'^theorem ',(B/'ReviewClient.lean.txt').read_text(),re.M)),'all_local_declarations_audited':len(rows),'module_audit_counts':{m:sum(x.startswith('DECL|'+m+'|') for x in rows) for m in mods+['ReviewClient']},'source_sha256':{m:sha(A/(m+'.lean')) for m in mods},'frozen_before_after':before,'steps':steps,'environment':json.loads((B/'environment.json').read_text()),'boundary':'Pinned prebuilt third-party dependencies are reused; every local source rebuilt; no project build cache.'}
(B/'lean-review.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',flush=True)
