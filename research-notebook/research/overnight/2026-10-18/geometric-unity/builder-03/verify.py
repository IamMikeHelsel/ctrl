"""Builder self-check of actual real adjoint. Independent acceptance is separate."""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile,time
B=Path(__file__).resolve().parent;R=B.parents[4];BASE=R/'lean-controls'
INHERITED=['CliffordModel','HyperbolicSpinor','SpinorDimensions','SplitSpinor','FockOperators','VacuumProjector','FockImage','WordActions','MatrixUnits','FullImage','RealEquivalence','OrderControls','BasisActions']
MODS=INHERITED+['TransposeBridge','VolumeForm','RealAdjoint','AdjointControls']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
PINS={'builder-02':'fab7240941cb89b4517fd2614160f7ebf122eff095b017f4676bd09cd94b792d',
 'critic-02':'7984208c7cd519eb42eceb8264d6047af00c0d5869548d1ad17e57fcf4895c73',
 'analyst-01':'0c667224d83d64fc6cd9b764e1a556da23e5c7f90ef462b5f5f35149e60f579e',
 'critic-01':'d525512033db6160c60ee77cc032a68e103253fa6604c620deb79077d4e640d3'}
def frozen_check():
 result={}
 for folder,digest in PINS.items():
  root=B.parent/folder;manifest=root/'SHA256SUMS'
  assert sha(manifest)==digest,(folder,'manifest changed')
  lines=manifest.read_text().splitlines()
  for line in lines:
   expected,name=line.split('  ',1);assert sha(root/name)==expected,(folder,name)
  result[folder]={'manifest_sha256':digest,'files_verified':len(lines)}
 for m in INHERITED:assert sha(B/(m+'.lean'))==sha(B.parent/'builder-02'/(m+'.lean'))
 return result
frozen=frozen_check()
source_freeze=json.loads((B/'source-freeze.json').read_text())
for p,h in source_freeze['files'].items():assert sha(B/p)==h,p
manifest=json.loads((BASE/'lake-manifest.json').read_text())
mathlib=next(x for x in manifest['packages'] if x['name']=='mathlib')['rev']
assert mathlib=='56a005855ea17e0b0958f73ec801ae140b0a1679'
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=BASE,env=env,text=True).strip().split(':')
# Exclude all project build products. Only pinned third-party dependency products are reused.
depaths=[str((BASE/p).resolve()) for p in paths if str((BASE/p).resolve())!=str(BASE/'.lake/build/lib/lean')]
env['PATH']=str(Path(lean).parent)+':'+env['PATH'];records=[]
def run(label,args,cwd,bad=False):
 start=time.monotonic();p=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
 (B/'logs'/(label+'.log')).write_text(p.stdout)
 records.append({'label':label,'command':args,'returncode':p.returncode,'seconds':round(time.monotonic()-start,3)})
 (B/'run-progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,p.returncode,flush=True)
 assert (p.returncode!=0 if bad else p.returncode==0),p.stdout
 if bad:assert not any(w in p.stdout.lower() for w in ['unknown identifier','unknown module','file not found','failed to synthesize'])
 return p.stdout
with tempfile.TemporaryDirectory(prefix='real-adjoint-fresh-',dir=B/'cache') as td:
 t=Path(td);env['LEAN_PATH']=str(t)+':'+':'.join(depaths);names=[]
 for m in MODS:
  source=(B/(m+'.lean')).read_text()
  assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',source)
  (t/(m+'.lean')).write_text(source)
  run('fresh-'+m,[lean,'--root='+str(t),'-o',str(t/(m+'.olean')),str(t/(m+'.lean'))],t)
  ns='GUClifford' if m=='CliffordModel' else 'HyperbolicSpinor'
  names += [ns+'.'+n for n in re.findall(r'^(?:@\[[^\n]*\]\s+)?(?:def|abbrev|theorem|lemma)\s+([^\s(:]+)',source,re.M)]
 audit='import AdjointControls\nimport OrderControls\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 (B/'Audit.lean.txt').write_text(audit);(t/'Audit.lean').write_text(audit)
 output=run('axioms',[lean,str(t/'Audit.lean')],t)
 axioms={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",output)}
 axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",output)})
 assert set(axioms)==set(names),set(names)-set(axioms)
 assert all(set(v)<={'propext','Quot.sound','Classical.choice'} for v in axioms.values())
 for m in MODS:run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'],t)
 client=(B/'Client.lean.txt').read_text();(t/'Client.lean').write_text(client)
 run('client',[lean,'--root='+str(t),'-o',str(t/'Client.olean'),str(t/'Client.lean')],t)
 run('kernel-Client',[str(Path(lean).with_name('leanchecker')),'Client','-v'],t)
 negatives={
 'EuclideanSkew':'''example : (positiveMatrix 0).transpose = -positiveMatrix 0 := by
  rw [positive_transpose]
''',
 'WrongNegative':'''example : (creationMatrix 0 + contractionMatrix 0) * (creationMatrix 0 + contractionMatrix 0) = -1 := by
  have hp : creationMatrix 0 + contractionMatrix 0 = positiveMatrix 0 := by rw [positiveMatrix_fock, add_comm]
  rw [hp, positive_zero_square]
''',
 'MissingK':'''example : K * (positiveMatrix 0).transpose = -positiveMatrix 0 := by
  rw [positive_transpose]
''',
 'WrongKSquare':'''example : K*K = -1 := by
  rw [K_square]
''',
 'WrongVectorBar':'''example : splitMatrixEquiv (star (gamma 0)) = positiveMatrix 0 := by
  change splitMatrix (star (gamma 0)) = positiveMatrix 0
  rw [splitMatrix_star]
  change realAdjoint (positiveMatrix 0) = positiveMatrix 0
  rw [realAdjoint_positive]
''',
 'PlainComplexTranspose':'''example : ((Complex.I : ℂ) • (1 : ComplexSpinMatrix)).transpose = -(Complex.I • (1 : ComplexSpinMatrix)) := by
  ext I J
  simp [Matrix.transpose_apply, Matrix.one_apply]
'''}
 for name,body in negatives.items():
  source='import AdjointControls\nnoncomputable section\nopen HyperbolicSpinor GUClifford\n'+body
  (B/(name+'.lean.txt')).write_text(source);(t/(name+'.lean')).write_text(source)
  run('negative-'+name,[lean,str(t/(name+'.lean'))],t,True)
 for p,h in source_freeze['files'].items():assert sha(B/p)==h,p
 assert frozen_check()==frozen
 result={'status':'PASS','scope':'builder self-check; independent acceptance pending',
  'source_freeze_sha256':sha(B/'source-freeze.json'),'source_sha256':{m:sha(B/(m+'.lean')) for m in MODS},
  'fresh_modules':len(MODS),'public_declarations':names,'public_count':len(names),'axioms':axioms,'steps':records,
  'lean':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),'mathlib':mathlib,
  'frozen_prior_evidence':frozen,'inherited_sources_preserved':True,'project_cache_excluded':True,
  'proved':['actual creation transpose equals contraction','actual positive and negative transpose laws','ordered actual negative product symmetric and involutive','actual algebra equivalence intertwines real Clifford conjugation and K-transpose-K'],
  'limits':['real coefficients only','complex scalar extension and Hermitian signature not proved here','no GU operator selection','no field-equation, physics or novelty result','pinned prebuilt Mathlib dependencies reused']}
 (B/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',flush=True)
