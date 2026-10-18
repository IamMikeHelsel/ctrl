"""Rebuild inherited sources and new result in a fresh isolated directory."""
from pathlib import Path
import os,subprocess,hashlib,json,tempfile,time
B=Path(__file__).resolve().parent
R=Path('/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes')
L=R/'lean-controls';old=R/'research/overnight/2026-10-18/geometric-unity/builder-05'
mods=['CliffordModel','HyperbolicSpinor','SpinorDimensions','SplitSpinor','FockOperators','VacuumProjector','FockImage','WordActions','MatrixUnits','FullImage','RealEquivalence','OrderControls','BasisActions','TransposeBridge','VolumeForm','RealAdjoint','AdjointControls','ComplexAdjoint','ComplexEquivalence','ComplexBridge','ComplexControls','ComplementAction','SplitSignature','ComplexSignature','SignatureControls']
T=Path(tempfile.mkdtemp(prefix='gu-skew-',dir=B));env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=L,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=L,env=env,text=True).strip().split(':')
deps=[str((L/p).resolve()) for p in paths if (L/p).resolve()!=(L/'.lake/build/lib/lean').resolve()]
env['LEAN_PATH']=':'.join([str(T)]+deps)
report={'lean':subprocess.check_output([lean,'--version'],text=True).strip(),'mathlib':subprocess.check_output(['git','rev-parse','HEAD'],cwd=L/'.lake/packages/mathlib',text=True).strip(),'dependency_manifest_sha256':hashlib.sha256((old/'SHA256SUMS').read_bytes()).hexdigest(),'sources':{},'steps':[]}
assert '4.35.0' in report['lean'] and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in report['lean']
assert report['mathlib']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=L/'.lake/packages/mathlib',text=True).strip()
assert hashlib.sha256((B.parent/'research-audit/VolumeTwist.lean').read_bytes()).hexdigest()=='97e602b6664e5f0635ef344e01e8761077da2354f7021d6e8d776438f4f8041d'
for line in (old/'SHA256SUMS').read_text().splitlines():
 digest,rel=line.split('  ',1)
 assert hashlib.sha256((old/rel).read_bytes()).hexdigest()==digest,rel
def run(m):
 p=subprocess.run([lean,'-o',str(T/(m+'.olean')),str(T/(m+'.lean'))],cwd=T,env=env,text=True,capture_output=True)
 (T/(m+'.log')).write_text(p.stdout+p.stderr);report['steps'].append({'module':m,'exit':p.returncode});print(m,p.returncode,flush=True)
 assert p.returncode==0,p.stdout+p.stderr
for m in mods+['SkewLie','Chirality','VolumeTwist','ComplexChoices','SpinEquivariance','HermitianFamily']:
 src=(old if m in mods else B.parent/'research-audit' if m=='VolumeTwist' else B.parent/'spin' if m=='SpinEquivariance' else B)/(m+'.lean');data=src.read_bytes();report['sources'][m]=hashlib.sha256(data).hexdigest();(T/(m+'.lean')).write_bytes(data);run(m)
(T/'Audit.lean').write_text('''import HermitianFamily
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  if let some i := env.getModuleIdxFor? n then
   if #[`SkewLie, `Chirality, `VolumeTwist, `ComplexChoices, `SpinEquivariance, `HermitianFamily].contains env.allImportedModuleNames[i.toNat]! then
    if info.isAxiom || info.isUnsafe then throwError "untrusted declaration: {n}"
    let axs ← collectAxioms n
    for a in axs do
     unless #[`propext, `Classical.choice, `Quot.sound].contains a do
      throwError "unexpected axiom {a} in {n}"
    logInfo m!"{n}: {axs}"
''');run('Audit')
report['build_directory']=str(T);(B/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
