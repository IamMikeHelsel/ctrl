"""Draft self-check: fresh local modules, standard axioms, kernel replay.
Independent review remains a coordinator task.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile,time
B=Path(__file__).resolve().parent;R=B.parents[4];BASE=R/'lean-controls'
MODS=['CliffordModel','HyperbolicSpinor','SpinorDimensions','SplitSpinor']
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan')
lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=BASE,env=env,text=True).strip().split(':')
depaths=[str((BASE/p).resolve()) for p in paths];env['PATH']=str(Path(lean).parent)+':'+env['PATH']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=R/'research/pods/2026-10-17/weinstein/clifford-contraction-03/builder/CliffordModel.lean'
assert sha(old)==sha(B/'CliffordModel.lean')
records=[]
def run(label,args,cwd,bad=False):
 start=time.monotonic();p=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 (B/'logs'/(label+'.log')).write_text(p.stdout)
 records.append({'label':label,'command':args,'returncode':p.returncode,'seconds':round(time.monotonic()-start,3)})
 print(label,p.returncode,flush=True)
 assert (p.returncode!=0 if bad else p.returncode==0),p.stdout
 if bad:
  assert not any(w in p.stdout.lower() for w in ['unknown identifier','unknown module','file not found'])
 return p.stdout
hashes={m:sha(B/(m+'.lean')) for m in MODS}
with tempfile.TemporaryDirectory(prefix='spinor-draft-',dir=B/'cache') as td:
 t=Path(td);env['LEAN_PATH']=str(t)+':'+':'.join(depaths)
 names=[]
 for m in MODS:
  source=(B/(m+'.lean')).read_text()
  assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',source)
  (t/(m+'.lean')).write_text(source)
  run('fresh-'+m,[lean,'--root='+str(t),'-o',str(t/(m+'.olean')),str(t/(m+'.lean'))],t)
  ns='GUClifford' if m=='CliffordModel' else 'HyperbolicSpinor'
  names += [ns+'.'+n for n in re.findall(r'^(?:@\[[^\n]*\]\s+)?(?:def|abbrev|theorem|lemma)\s+([^\s(:]+)',source,re.M)]
 audit='import SplitSpinor\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 (B/'Audit.lean.txt').write_text(audit);(t/'Audit.lean').write_text(audit)
 output=run('axioms',[lean,str(t/'Audit.lean')],t)
 axioms={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",output)}
 axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",output)})
 assert set(axioms)==set(names),(set(names)-set(axioms))
 assert all(set(v)<={'propext','Quot.sound','Classical.choice'} for v in axioms.values())
 for m in MODS:run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'],t)
 client='''import SplitSpinor
open HyperbolicSpinor GUClifford
example : Module.finrank ℝ S7 = 128 := spinor_finrank
example : Module.finrank ℝ Cl = 16384 := clifford_finrank
example (a b : Cl) : splitMatrix (a*b) = splitMatrix a * splitMatrix b := splitMatrix_mul a b
example : splitMatrix (gamma 0) ≠ 0 := positive_not_zero
example : splitMatrix (gamma 7) * splitMatrix (gamma 7) ≠ 1 := negative_square_not_positive
'''
 (B/'Client.lean.txt').write_text(client);(t/'Client.lean').write_text(client)
 run('client',[lean,str(t/'Client.lean')],t)
 negative='''import SplitSpinor
open HyperbolicSpinor GUClifford
example : splitMatrix (gamma 7) * splitMatrix (gamma 7) = 1 := by
  exact negative_square
'''
 (B/'WrongSquare.lean.txt').write_text(negative);(t/'WrongSquare.lean').write_text(negative)
 run('negative-square',[lean,str(t/'WrongSquare.lean')],t,True)
 original=(B/'HyperbolicSpinor.lean').read_text()
 mutant=original.replace('cliffordVector R M p (cliffordVector R M p x) = p.1 p.2 • x','cliffordVector R M p (cliffordVector R M p x) = (2 * p.1 p.2) • x',1)
 assert mutant!=original
 (B/'WrongFactor.lean.txt').write_text(mutant);(t/'WrongFactor.lean').write_text(mutant)
 run('negative-factor',[lean,str(t/'WrongFactor.lean')],t,True)
 assert hashes=={m:sha(B/(m+'.lean')) for m in MODS}
 assert sha(old)==sha(B/'CliffordModel.lean')
 result={'status':'pass','scope':'builder self-check; no independent review yet','source_sha256':hashes,
  'public_declarations':names,'axioms':axioms,'steps':records,
  'lean':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),
  'mathlib':'56a005855ea17e0b0958f73ec801ae140b0a1679',
  'inherited_source':str(old.relative_to(R)),'inherited_source_preserved':True,
  'limits':['No surjectivity or injectivity of splitMatrix','No matrix-adjoint bridge','No Hermitian signature theorem','No GU operator selected','Pinned prebuilt Mathlib reused']}
 (B/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print('PASS',flush=True)
