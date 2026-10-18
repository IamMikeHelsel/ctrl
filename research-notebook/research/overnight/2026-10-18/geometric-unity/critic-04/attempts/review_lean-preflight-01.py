"""Independent frozen-source reconstruction and client review, no builder runner import."""
from pathlib import Path
import json, hashlib, subprocess, os, re, time
D=Path(__file__).resolve().parent; R=D.parents[4]; B=D.parent/'builder-04'; L=R/'lean-controls'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected='861cd093c525217d7f9f04dbee0ff22889efd541e746bc7a82eeea9a20c4a8c9'
def freeze():
 assert sha(B/'SHA256SUMS')==expected
 lines=(B/'SHA256SUMS').read_text().splitlines()
 for line in lines:
  h,p=line.split('  ',1); assert sha(B/p)==h,(p,h)
 return {'manifest':expected,'files':len(lines)}
before=freeze()
# Discover local closure from actual imports, and sort it without trusting builder module order.
sources={p.stem:p for p in B.glob('*.lean')}
imports={m:re.findall(r'^import\s+([^\n]+)',p.read_text(),re.M) for m,p in sources.items()}
order=[];active=set()
def visit(m):
 if m in order:return
 assert m not in active,('cycle',m)
 active.add(m)
 for line in imports[m]:
  for dep in line.split():
   if dep in sources:visit(dep)
   else:assert dep.startswith(('Mathlib.','Lean.')),('unknown',dep)
 active.remove(m);order.append(m)
visit('ComplexControls');assert set(order)==set(sources),(order,sources.keys())
T=D/'cache'/'fresh-01';assert not T.exists();T.mkdir(parents=True)
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');lake=str(R/'.tools/elan/bin/lake')
def output(cmd,cwd=L):return subprocess.check_output(cmd,cwd=cwd,env=env,text=True).strip()
lean=Path(output([lake,'env','which','lean']));version=output([str(lean),'--version'])
assert '4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version
pin='56a005855ea17e0b0958f73ec801ae140b0a1679'
assert next(p for p in json.loads((L/'lake-manifest.json').read_text())['packages'] if p['name']=='mathlib')['rev']==pin
assert output(['git','rev-parse','HEAD'],L/'.lake/packages/mathlib')==pin
assert output(['git','status','--porcelain'],L/'.lake/packages/mathlib')==''
paths=[(L/p).resolve() for p in output([lake,'env','printenv','LEAN_PATH']).split(':')]
deps=[p for p in paths if p!=(L/'.lake/build/lib/lean').resolve()]
assert all('/.lake/packages/' in str(p) or p==lean.parent.parent/'lib/lean' for p in deps),deps
env['LEAN_PATH']=':'.join(map(str,[T]+deps));env['PATH']=str(lean.parent)+':'+env['PATH']
(D/'environment.json').write_text(json.dumps({'lean':version,'mathlib':pin,'paths':env['LEAN_PATH'],'excluded_project_cache':True},indent=2)+'\n')
steps=[]
def run(name,cmd,negative=False):
 start=time.monotonic();r=subprocess.run(cmd,cwd=T,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
 (D/'logs'/(name+'.txt')).write_text(r.stdout)
 steps.append({'name':name,'code':r.returncode,'seconds':time.monotonic()-start,'command':cmd})
 (D/'run-progress.json').write_text(json.dumps(steps,indent=2)+'\n');print(name,r.returncode,flush=True)
 if negative:
  assert r.returncode!=0
  assert 'unsolved goals' in r.stdout or 'Type mismatch' in r.stdout or 'type mismatch' in r.stdout,r.stdout
  assert not any(s in r.stdout.lower() for s in ['unknown identifier','unknown module','file not found','failed to synthesize']),r.stdout
 else:assert r.returncode==0,r.stdout
 return r.stdout
for m in order:
 txt=sources[m].read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',txt)
 (T/(m+'.lean')).write_bytes(sources[m].read_bytes())
 run('fresh-'+m,[str(lean),'--root='+str(T),'-o',str(T/(m+'.olean')),str(T/(m+'.lean'))])
(T/'ReviewClient.lean').write_bytes((D/'ReviewClient.lean.txt').read_bytes())
run('ReviewClient',[str(lean),'--root='+str(T),'-o',str(T/'ReviewClient.olean'),str(T/'ReviewClient.lean')])
audit='''import ReviewClient
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
 let env ← getEnv
 let owned : Array Name := #[MODULES]
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
'''.replace('MODULES',', '.join('`'+m for m in order+['ReviewClient']))
(D/'Audit.lean.txt').write_text(audit);(T/'Audit.lean').write_text(audit)
rows=run('audit',[str(lean),str(T/'Audit.lean')]);rows=[s for s in rows.splitlines() if s.startswith('DECL|')];assert rows
negatives={
'FalseImaginaryFixed':'example : complexMatrixEquiv (bar (Complex.I ⊗ₜ[ℝ] (1 : Cl))) = complexMatrixEquiv (Complex.I ⊗ₜ[ℝ] (1 : Cl)) := by\n rw [bar_tmul]\n simp only [star_one, complexMatrixEquiv_tmul, map_one]\n',
'FalsePointwiseProduct':'example : (E01*E10) (∅ : Finset J) ∅ = E01 ∅ ∅ * E10 ∅ ∅ := by\n simp only [E01, E10, Matrix.single_mul_single]\n',
'FalseCommutingImages':'example : complexMatrixEquiv.symm E01 * complexMatrixEquiv.symm E10 = complexMatrixEquiv.symm E10 * complexMatrixEquiv.symm E01 := by\n apply complexMatrixEquiv.injective\n simp only [map_mul, complexMatrixEquiv.apply_symm_apply]\n',
'FalseConjugatedForwardMap':'example : complexMatrixEquiv (Complex.I ⊗ₜ[ℝ] (1 : Cl)) = -Complex.I • (1 : CMatrix) := by\n rw [pure_scalar_unconjugated]\n',
'FalseBarLinear':'example : complexMatrixEquiv (bar (Complex.I • (1 : CCl))) = Complex.I • complexMatrixEquiv (bar (1 : CCl)) := by\n rw [complexMatrixEquiv_bar_I]\n simp only [bar, star_one, map_one]\n',
'FalseIdentitySkew':'example : Skew (1 : CCl) := by\n unfold Skew bar\n simp only [star_one]\n',
'FalseTranspose':'example : complexMatrixEquiv (bar (Complex.I • (1 : CCl))) = Kc*(complexMatrixEquiv (Complex.I • (1 : CCl))).transpose*Kc := by\n rw [complexMatrixEquiv_bar_I, complexMatrixEquiv_I, Matrix.transpose_smul, Matrix.transpose_one, mul_smul_comm, mul_one, smul_mul_assoc, Kc_square]\n'}
for n,body in negatives.items():
 src='import ReviewClient\nnoncomputable section\nopen scoped TensorProduct\nopen HyperbolicSpinor GUClifford GUComplex IndependentComplexReview\n'+body
 (D/(n+'.lean.txt')).write_text(src);(T/(n+'.lean')).write_text(src)
 run(n,[str(lean),str(T/(n+'.lean'))],True)
for m in order+['ReviewClient']:run('kernel-'+m,[str(lean.with_name('leanchecker')),m,'-v'])
assert freeze()==before
result={'status':'PASS','fresh_modules':len(order),'module_order':order,'client_theorems':len(re.findall(r'^theorem ',(D/'ReviewClient.lean.txt').read_text(),re.M)),'all_local_declarations_audited':len(rows),'module_audit_counts':{m:sum(x.startswith('DECL|'+m+'|') for x in rows) for m in order+['ReviewClient']},'negative_controls':len(negatives),'kernel_checks':len(order)+1,'before_after':before,'source_sha256':{m:sha(p) for m,p in sources.items()},'steps':steps,'boundary':'Fresh all-local closure; pinned prebuilt dependency cache remains trusted.'}
(D/'lean-review.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',flush=True)
