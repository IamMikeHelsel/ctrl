from pathlib import Path
import os,json,subprocess,re,time,hashlib
B=Path(__file__).resolve().parent
E=json.loads((B/'environment.json').read_text());T=B/'cache/review-01'
env=os.environ.copy()
for key in ['LEAN_PATH','ELAN_HOME','PATH']:env[key]=E[key]
lean=E['compiler'];steps=[]
assert all((T/(m+'.olean')).exists() for m in E['module_order']), 'Full local fresh rebuild first'
def run(name,source=None,negative=False,checker=False):
    if source is not None:(T/(name+'.lean')).write_text(source)
    cmd=([str(Path(lean).with_name('leanchecker')),name,'-v'] if checker else [lean,'--root='+str(T),'-o',str(T/(name+'.olean')),str(T/(name+'.lean'))])
    start=time.monotonic();p=subprocess.run(cmd,cwd=T,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    label=('kernel-' if checker else '')+name
    (B/'logs'/(label+'.txt')).write_text(p.stdout)
    steps.append({'name':label,'returncode':p.returncode,'seconds':time.monotonic()-start,'command':cmd})
    (B/'client-progress.json').write_text(json.dumps(steps,indent=2)+'\n')
    print(label,p.returncode,flush=True)
    if negative:
        assert p.returncode!=0
        assert 'unsolved goals' in p.stdout,p.stdout
        assert not any(w in p.stdout.lower() for w in ['unknown identifier','unknown module','type mismatch','unexpected token','failed to synthesize','file not found']),p.stdout
    else:assert p.returncode==0,p.stdout
    return p.stdout
src=(B/'clients/ReviewerClient.lean').read_text()
run('ReviewerClient',src)
run('ReviewerClient',checker=True)
negatives={
'FalseMissingSign':'example : K *ᵥ unitCoord {6} = unitCoord ({6} : Finset J)ᶜ := by\n  rw [ReviewerSignature.singleton_last_sign]\n  ext T\n  simp [unitCoord, Pi.single_apply]\n',
'FalseMissingComplement':'example : K ∅ ∅ = 1 := by\n  rw [K_zero_diagonal]\n  norm_num\n',
'FalseUnitForm':'example : (U.transpose * K * U) ∅ ∅ = 1 := by\n  rw [real_positive_direction]\n  norm_num\n',
'FalseNegativeIsPositive':'example : (U.transpose * K * U) {0,6} {0,6} = 2 := by\n  rw [ReviewerSignature.real_negative_value]\n  norm_num\n',
'FalseComplexIsPositive':'example : (Uc.conjTranspose * Kc * Uc) {0,6} {0,6} = 2 := by\n  rw [ReviewerSignature.complex_negative_value]\n  norm_num\n',
'FalseTransposeInverse':'example : (U.transpose * U) ∅ ∅ = 1 := by\n  rw [U_orthogonal_scaled]\n  norm_num\n',
'FalseHalfCount':'example : (Finset.univ.filter (fun T : Finset J => (0 : J) ∉ T)).card = 63 := by\n  rw [positive_half_count]\n  norm_num\n',
'FalseImaginaryFixed':'example : complexMatrixEquiv (bar (Complex.I • (1 : CCl))) ∅ ∅ = Complex.I := by\n  rw [complexMatrixEquiv_bar_I]\n  norm_num [Matrix.one_apply, Complex.ext_iff]\n',
'FalseProjectorIdentity':'example : ((1+K) *ᵥ (unitCoord ∅ - K *ᵥ unitCoord ∅)) ∅ = 1 := by\n  rw [unpaired_projector_kills]\n  norm_num\n'
}
header='import ReviewerClient\nnoncomputable section\nopen Matrix HyperbolicSpinor GUComplex GUClifford\n'
for n,body in negatives.items():
    (B/'clients'/(n+'.lean.txt')).write_text(header+body)
    run(n,header+body,negative=True)
mods=E['module_order']+['ReviewerClient']
audit='''import ReviewerClient
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let owned : Array Name := #[MODULES]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[i.toNat]!
      if owned.contains origin then
        if info.isUnsafe then throwError "Unsafe owned declaration: {n}"
        if info.isAxiom then throwError "Owned axiom: {n}"
        let axioms ← collectAxioms n
        for ax in axioms do
          unless allowed.contains ax do throwError "Unexpected axiom: {n}: {ax}"
        logInfo m!"AUDIT|{origin}|{n}|{info.isTheorem}|{axioms}"
'''.replace('MODULES',', '.join('`'+m for m in mods))
(B/'clients/Audit.lean').write_text(audit)
out=run('Audit',audit)
rows=[line for line in out.splitlines() if line.startswith('AUDIT|')]
counts={m:sum(line.startswith('AUDIT|'+m+'|') for line in rows) for m in mods}
assert all(c>0 for c in counts.values()),counts
(B/'client-result.json').write_text(json.dumps({'status':'PASS','positive_client_theorems':len(re.findall(r'^theorem ',src,re.M)),'negative_clients':len(negatives),'negative_criterion':'Every false client must leave unsolved mathematical goals; infrastructure and type mismatch failures reject the review.','all_local_declarations':len(rows),'module_counts':counts,'steps':steps},indent=2)+'\n')
