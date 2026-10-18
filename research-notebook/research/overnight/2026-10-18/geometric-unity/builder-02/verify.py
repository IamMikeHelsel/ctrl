"""Builder self-check. Fresh reviewer acceptance is a separate gate."""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile,time
B=Path(__file__).resolve().parent;R=B.parents[4];BASE=R/'lean-controls'
MODS=['CliffordModel','HyperbolicSpinor','SpinorDimensions','SplitSpinor','FockOperators','VacuumProjector','FockImage','WordActions','MatrixUnits','FullImage','RealEquivalence','OrderControls','BasisActions']
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan')
lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=BASE,env=env,text=True).strip().split(':')
depaths=[str((BASE/p).resolve()) for p in paths];env['PATH']=str(Path(lean).parent)+':'+env['PATH']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
PINS={'analyst-01':'0c667224d83d64fc6cd9b764e1a556da23e5c7f90ef462b5f5f35149e60f579e','critic-01':'d525512033db6160c60ee77cc032a68e103253fa6604c620deb79077d4e640d3'}
def frozen_check():
 result={}
 for folder,digest in PINS.items():
  root=B.parent/folder; manifest=root/'SHA256SUMS'
  assert sha(manifest)==digest,(folder,'manifest changed')
  count=0
  for line in manifest.read_text().splitlines():
   expected,name=line.split('  ',1)
   assert sha(root/name)==expected,(folder,name)
   count+=1
  result[folder]={'manifest_sha256':digest,'files_verified':count}
 for m in MODS[:4]:assert sha(B/(m+'.lean'))==sha(B.parent/'analyst-01'/(m+'.lean'))
 return result
frozen=frozen_check()
manifest=json.loads((BASE/'lake-manifest.json').read_text())
mathlib=next(x for x in manifest['packages'] if x['name']=='mathlib')['rev']
assert mathlib=='56a005855ea17e0b0958f73ec801ae140b0a1679'
records=[]
def run(label,args,cwd,bad=False):
 start=time.monotonic();p=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=240)
 (B/'logs'/(label+'.log')).write_text(p.stdout)
 records.append({'label':label,'command':args,'returncode':p.returncode,'seconds':round(time.monotonic()-start,3)})
 print(label,p.returncode,flush=True)
 assert (p.returncode!=0 if bad else p.returncode==0),p.stdout
 if bad:assert not any(w in p.stdout.lower() for w in ['unknown identifier','unknown module','file not found','failed to synthesize'])
 return p.stdout
hashes={m:sha(B/(m+'.lean')) for m in MODS}
with tempfile.TemporaryDirectory(prefix='matrix-units-fresh-',dir=B/'cache') as td:
 t=Path(td);env['LEAN_PATH']=str(t)+':'+':'.join(depaths)
 names=[]
 for m in MODS:
  source=(B/(m+'.lean')).read_text()
  assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',source)
  (t/(m+'.lean')).write_text(source)
  run('fresh-'+m,[lean,'--root='+str(t),'-o',str(t/(m+'.olean')),str(t/(m+'.lean'))],t)
  ns='GUClifford' if m=='CliffordModel' else 'HyperbolicSpinor'
  names += [ns+'.'+n for n in re.findall(r'^(?:@\[[^\n]*\]\s+)?(?:def|abbrev|theorem|lemma)\s+([^\s(:]+)',source,re.M)]
 audit='import OrderControls\nimport BasisActions\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 (B/'Audit.lean.txt').write_text(audit);(t/'Audit.lean').write_text(audit)
 output=run('axioms',[lean,str(t/'Audit.lean')],t)
 axioms={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",output)}
 axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",output)})
 assert set(axioms)==set(names),(set(names)-set(axioms))
 assert all(set(v)<={'propext','Quot.sound','Classical.choice'} for v in axioms.values())
 for m in MODS:run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'],t)
 client='''import OrderControls
import BasisActions
open HyperbolicSpinor GUClifford
example (I J T : Finset (Fin 7)) :
    splitAction (matrixUnitElement I J) (spinBasis T) = if J=T then spinBasis I else 0 := by
  rw [matrixUnit_image, matrixUnit_basis]
example (T : Finset (Fin 7)) : splitAction vacuumElement (spinBasis T) = if T=∅ then 1 else 0 := by
  rw [vacuum_image, vacuum_basis]
example : vacuum * vacuum = vacuum := vacuum_idempotent
example (f : Module.End ℝ S7) : splitAction (preimage f) = f := preimage_image f
example : Function.Bijective splitMatrix := ⟨splitMatrix_injective, splitMatrix_surjective⟩
example : Cl ≃ₐ[ℝ] Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ := splitMatrixEquiv
example (i : J) (T : Finset J) (h : i ∉ T) :
    ∃ A B : List J, ordered (insert i T) = A++i::B ∧ ordered T=A++B ∧
    create i (spinBasis T) = (-1 : ℝ)^A.length • spinBasis (insert i T) := create_basis_absent_exact i T h
example (i : J) (T : Finset J) (h : i ∈ T) :
    ∃ A B : List J, ordered T=A++i::B ∧
    annihilate i (spinBasis T) = (-1 : ℝ)^A.length • spinBasis (T.erase i) := annihilate_basis_present_exact i T h
example : vacuum (annihilators [0,1] (word [0,1])) = (1 : S7) := correctTwoOrder
example : vacuum ((annihilate 0 * annihilate 1) (word [0,1])) = (-1 : S7) := wrongTwoOrder
'''
 (B/'Client.lean.txt').write_text(client);(t/'Client.lean').write_text(client)
 run('client',[lean,str(t/'Client.lean')],t)
 negatives={
 'WrongFactor':'''example : (create 0 * annihilate 0) (1 : S7) = 1 := by
  rw [wrongFactor_vacuum]
''',
 'WrongSign':'''example : splitAction (wrongAnnihilatorElement 0) (create 0 (1 : S7)) = 1 := by
  rw [wrongAnnihilator_created_vacuum]
''',
 'WrongOrder':'''example : vacuum ((annihilate 0 * annihilate 1) (word [0,1])) = (1 : S7) := by
  rw [wrongTwoOrder]
'''}
 for name,body in negatives.items():
  source='import OrderControls\nopen HyperbolicSpinor GUClifford\n'+body
  (B/(name+'.lean.txt')).write_text(source);(t/(name+'.lean')).write_text(source)
  run('negative-'+name,[lean,str(t/(name+'.lean'))],t,True)
 assert hashes=={m:sha(B/(m+'.lean')) for m in MODS}
 assert frozen_check()==frozen
 result={'status':'pass','scope':'builder self-check; independent review pending','source_sha256':hashes,
  'public_declarations':names,'axioms':axioms,'steps':records,
  'lean':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),'mathlib':mathlib,
  'frozen_prior_evidence':frozen,'inherited_sources_preserved':True,
  'proved':['actual basis creation and contraction with position signs','vacuum projection on every exterior basis vector','all actual Clifford matrix units','explicit preimage of every endomorphism','surjective and injective concrete split representation','real algebra equivalence'],
  'limits':['real coefficients only','no complex adjoint bridge or Hermitian signature proof','no choice of GU operator Phi','no field-equation, physics, or novelty claim','pinned prebuilt Mathlib dependencies reused']}
 (B/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print('PASS',flush=True)
