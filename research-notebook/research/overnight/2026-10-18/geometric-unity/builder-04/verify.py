"""Fresh builder self-check. Independent acceptance remains a separate gate."""
from pathlib import Path
import os, subprocess, hashlib, json, re, time
B=Path(__file__).resolve().parent;R=B.parents[4];L=R/'lean-controls';T=B/'cache'/'fresh-01'
mods=['CliffordModel','HyperbolicSpinor','SpinorDimensions','SplitSpinor','FockOperators','VacuumProjector','FockImage','WordActions','MatrixUnits','FullImage','RealEquivalence','OrderControls','BasisActions','TransposeBridge','VolumeForm','RealAdjoint','AdjointControls','ComplexAdjoint','ComplexEquivalence','ComplexBridge','ComplexControls']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={
 'research/overnight/2026-10-18/geometric-unity/builder-03':'3a6f59f0b26b0b60541fbb7d913be8dfb5c61ee0d7e8b9e10f8c36a1ae3ccf24',
 'research/overnight/2026-10-18/geometric-unity/critic-03':'a6af23a3104a95e72aa5141ce327369a947d478eacf333600df052d07a0bb23c',
 'research/overnight/2026-10-18/geometric-unity/builder-02':'fab7240941cb89b4517fd2614160f7ebf122eff095b017f4676bd09cd94b792d',
 'research/overnight/2026-10-18/geometric-unity/critic-02':'7984208c7cd519eb42eceb8264d6047af00c0d5869548d1ad17e57fcf4895c73',
 'research/overnight/2026-10-18/geometric-unity/analyst-01':'0c667224d83d64fc6cd9b764e1a556da23e5c7f90ef462b5f5f35149e60f579e',
 'research/overnight/2026-10-18/geometric-unity/critic-01':'d525512033db6160c60ee77cc032a68e103253fa6604c620deb79077d4e640d3',
 'research/pods/2026-10-17/weinstein/complex-adjoint-04/builder':'c498ef42bd3d8c428a0dcab1c34d4ca1eb41e419d57a47f00fdb6eca18cb7e0e',
 'research/pods/2026-10-17/weinstein/complex-adjoint-04/grader':'6c429ab23ededc5e5560d9b20cc0a957945e6b0c26dbeb49cc06ab9b79e4a6b8'}
def frozen():
 out={}
 for f,h in pins.items():
  d=R/f;m=d/'SHA256SUMS';assert sha(m)==h,(f,'manifest')
  lines=m.read_text().splitlines()
  for line in lines:
   expected,p=line.split('  ',1);assert sha(d/p)==expected,(f,p)
  out[f]={'manifest_sha256':h,'files':len(lines)}
 for m in mods[:17]:assert sha(B/(m+'.lean'))==sha(B.parent/'builder-03'/(m+'.lean'))
 assert sha(B/'ComplexAdjoint.lean')==sha(R/'research/pods/2026-10-17/weinstein/complex-adjoint-04/builder/ComplexAdjoint.lean')
 return out
before=frozen();freeze=json.loads((B/'source-freeze.json').read_text())
for p,h in freeze['files'].items():assert sha(B/p)==h,p
assert not T.exists(),'Fresh output directory required; preserve failed attempts.'
T.mkdir(parents=True)
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=L,env=env,text=True).strip()
version=subprocess.check_output([lean,'--version'],env=env,text=True).strip();assert '4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version
manifest=json.loads((L/'lake-manifest.json').read_text());mathlib=next(x for x in manifest['packages'] if x['name']=='mathlib')['rev'];assert mathlib=='56a005855ea17e0b0958f73ec801ae140b0a1679'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=L/'.lake/packages/mathlib',text=True).strip()==mathlib
assert not subprocess.check_output(['git','status','--porcelain'],cwd=L/'.lake/packages/mathlib',text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=L,env=env,text=True).strip().split(':')
deps=[str((L/p).resolve()) for p in paths if (L/p).resolve()!=(L/'.lake/build/lib/lean').resolve()]
assert all('/.lake/packages/' in p or Path(p)==Path(lean).parent.parent/'lib/lean' for p in deps),deps
env['LEAN_PATH']=str(T)+':'+':'.join(deps);env['PATH']=str(Path(lean).parent)+':'+env['PATH']
(B/'environment.json').write_text(json.dumps({'lean':version,'mathlib':mathlib,'lean_path':env['LEAN_PATH'],'project_cache_excluded':True,'development_cache_excluded':True},indent=2)+'\n')
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
 source=(B/(m+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source)
 (T/(m+'.lean')).write_bytes((B/(m+'.lean')).read_bytes())
 run('fresh-'+m,[lean,'--root='+str(T),'-o',str(T/(m+'.olean')),str(T/(m+'.lean'))])
(T/'Client.lean').write_bytes((B/'Client.lean.txt').read_bytes())
run('Client',[lean,'--root='+str(T),'-o',str(T/'Client.olean'),str(T/'Client.lean')])
audit='''import Client
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
'''.replace('OWNED',', '.join('`'+m for m in mods+['Client']))
(B/'Audit.lean.txt').write_text(audit);(T/'Audit.lean').write_text(audit)
aout=run('axioms',[lean,str(T/'Audit.lean')]);rows=[x for x in aout.splitlines() if x.startswith('DECL|')];assert rows
negative={
 'FalsePlainTranspose':'''example : complexMatrixEquiv (bar (Complex.I • (1 : CCl))) = Kc * (complexMatrixEquiv (Complex.I • (1 : CCl))).transpose * Kc := by
  rw [complexMatrixEquiv_bar_I, complexMatrixEquiv_I, Matrix.transpose_smul, Matrix.transpose_one, mul_smul_comm, mul_one, smul_mul_assoc, Kc_square]
''',
 'FalseScalarLinearity':'''example : complexMatrixEquiv (bar (Complex.I • (1 : CCl))) = Complex.I • complexMatrixEquiv (bar (1 : CCl)) := by
  rw [complexMatrixEquiv_bar_I]
  simp only [bar, star_one, map_one]
''',
 'FalseReversedProduct':'''example (a b : CCl) : complexMatrixEquiv (bar (a*b)) = complexMatrixEquiv (bar a) * complexMatrixEquiv (bar b) := by
  rw [bar_mul, map_mul]
''',
 'FalseConjugatedTensor':'''example : complexMatrixEquiv (Complex.I ⊗ₜ[ℝ] (1 : Cl)) = -Complex.I • (1 : CMatrix) := by
  simp only [complexMatrixEquiv_tmul, map_one]
''',
 'FalseCommutingPreimages':'''example : let a := complexMatrixEquiv.symm (Matrix.single (∅ : Finset J) {0} (1 : ℂ)); let b := complexMatrixEquiv.symm (Matrix.single ({0} : Finset J) ∅ (1 : ℂ)); a*b = b*a := by
  dsimp
  apply complexMatrixEquiv.injective
  simp only [map_mul, complexMatrixEquiv.apply_symm_apply]
'''}
for n,s in negative.items():
 src='import Client\nnoncomputable section\nopen scoped TensorProduct\nopen HyperbolicSpinor GUClifford GUComplex\n'+s
 (B/(n+'.lean.txt')).write_text(src);(T/(n+'.lean')).write_text(src)
 run(n,[lean,str(T/(n+'.lean'))],True)
for m in mods+['Client']:run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'])
assert frozen()==before
for p,h in freeze['files'].items():assert sha(B/p)==h,p
result={'status':'PASS','scope':'Builder self-check only; independent acceptance pending','fresh_modules':len(mods),'client_theorems':len(re.findall(r'^theorem ',(B/'Client.lean.txt').read_text(),re.M)),'all_local_declarations_audited':len(rows),'module_audit_counts':{m:sum(x.startswith('DECL|'+m+'|') for x in rows) for m in mods+['Client']},'source_sha256':{m:sha(B/(m+'.lean')) for m in mods},'source_freeze_sha256':sha(B/'source-freeze.json'),'frozen_before_after':before,'steps':steps,'environment':json.loads((B/'environment.json').read_text()),'boundary':'Pinned prebuilt third-party dependencies are reused; every local source rebuilt; no project or development build cache.'}
(B/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',flush=True)
