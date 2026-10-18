"""Independent E8 replay. Run in a review copy with no fresh/ directory.
Uses only pinned package products plus modules freshly built below.
"""
from pathlib import Path
import os, re, json, hashlib, shutil, subprocess, time
from datetime import datetime, timezone
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lean-controls').is_dir())
INPUT=HERE/'frozen-builder'
WORK=HERE/'fresh'
BIN=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
ALLOWED={'propext','Classical.choice','Quot.sound'}
MODULES=['Erdos128.WeightedGraph','Erdos128.CubicNeighborhood','Erdos128.OneStepSaving','WeightedProfiles','ProfileControls','CriticControls']
NS=['Erdos128','Erdos128','Erdos128','Erdos128.ProfileBridge','Erdos128.ProfileControls','CriticE8']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 assert sha(INPUT/'artifact-sha256.json')=='fe60ad304a8e66638b31bce37677ee158c52135b08a4aa128a59c03c58987e26'
 frozen=json.loads((INPUT/'artifact-sha256.json').read_text())['files']
 for p,h in frozen.items():assert sha(INPUT/p)==h,p
 WORK.mkdir(exist_ok=False)
 package_root=ROOT/'lean-controls/.lake/packages'
 deps=sorted(x/'.lake/build/lib/lean' for x in package_root.iterdir() if (x/'.lake/build/lib/lean').is_dir())
 assert sha(ROOT/'lean-controls/lean-toolchain')==sha(INPUT/'source-inputs/executed-lean-toolchain')
 assert sha(ROOT/'lean-controls/lake-manifest.json')==sha(INPUT/'source-inputs/executed-lake-manifest.json')
 pin=json.loads((ROOT/'lean-controls/lake-manifest.json').read_text())
 assert next(x['rev'] for x in pin['packages'] if x['name']=='mathlib')=='56a005855ea17e0b0958f73ec801ae140b0a1679'
 env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(str(x) for x in [WORK,*deps]);env['PATH']=str(BIN)+os.pathsep+env.get('PATH','')
 data={'started_utc':datetime.now(timezone.utc).isoformat(),'builder_manifest_sha256':sha(INPUT/'artifact-sha256.json'),'builder_files_verified':len(frozen),'lean_version':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),'lean_path':env['LEAN_PATH'],'pin':pin,'sources':{},'runs':[],'axioms':{},'passed':False}
 decls=[]
 for mod,ns in zip(MODULES,NS):
  rel=Path(mod.replace('.','/')).with_suffix('.lean')
  src=INPUT/'upstream-source'/rel if mod.startswith('Erdos128.') else (HERE/rel if mod=='CriticControls' else INPUT/rel)
  dest=WORK/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
  code=src.read_text()
  assert not re.search(r'\b(?:sorry|admit|native_decide|trustCompiler)\b|^\s*(?:axiom|unsafe)\b',code,re.M),mod
  names=re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+(\w+)',code,re.M)
  decls.extend(ns+'.'+x for x in names)
  data['sources'][mod]={'sha256':sha(src),'input':str(src.relative_to(HERE)),'copy':str(dest.relative_to(HERE)),'public_declarations':names,'imports':re.findall(r'^import\s+(.*)$',code,re.M)}
 audit='import CriticControls\nset_option pp.universes true\nset_option format.width 150\n'
 audit+='\n'.join('#print axioms '+x for x in decls)+'\n'
 for name in ['Erdos128.ProfileBridge.exists_affine_profile','Erdos128.ProfileBridge.mean_second_degree','Erdos128.ProfileBridge.objective_twoLevel','Erdos128.ProfileBridge.high_profile_mean']:
  audit+='#check @'+name+'\n'
 for name in ['Erdos128.RatProbabilityWeight','Erdos128.IsUnitProfile','Erdos128.weightedMean','Erdos128.weightedDegree','Erdos128.weightedSecondDegree','Erdos128.edgeMass','Erdos128.weightedObjective','Erdos128.ProfileBridge.lowProfile','Erdos128.ProfileBridge.highProfile']:
  audit+='#print '+name+'\n'
 (WORK/'ReviewAudit.lean').write_text(audit)
 data['declarations']=decls
 def save():
  (HERE/'verification.json').write_text(json.dumps(data,indent=2)+'\n')
 def run(label,args,negative=False):
  t=time.monotonic()
  try:
   r=subprocess.run(args,cwd=WORK,env=env,capture_output=True,text=True,timeout=180)
   out=r.stdout+r.stderr;rc=r.returncode
  except subprocess.TimeoutExpired as e:
   out=str(e.stdout or '')+'\n'+str(e.stderr or '')+'\nTIMEOUT';rc=124
  (WORK/(label+'.log')).write_text(out)
  ok=rc==0 if not negative else rc not in [0,124] and 'unsolved goals' in out and not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize',out)
  data['runs'].append({'label':label,'command':args,'returncode':rc,'expected_rejection':negative,'passed':bool(ok),'seconds':time.monotonic()-t,'log':'fresh/'+label+'.log'})
  save();print(label,rc,ok,flush=True)
  if not ok:raise RuntimeError(label)
  return out
 for mod in MODULES+['ReviewAudit']:
  rel=Path(mod.replace('.','/')).with_suffix('.lean')
  out=run('compile-'+mod.replace('.','-'),[str(BIN/'lean'),'-o',str(rel.with_suffix('.olean')),str(rel)])
  if mod=='ReviewAudit':
   axes={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
   axes.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",out)})
   assert set(axes)==set(decls),(set(decls)-set(axes),set(axes)-set(decls))
   assert all(set(x)<=ALLOWED for x in axes.values())
   data['axioms']=axes;save()
 for mod in MODULES+['ReviewAudit']:
  run('kernel-'+mod.replace('.','-'),[str(BIN/'leanchecker'),mod,'-v'])
 for name in ['BadTriangle','BadMean','BadNormalization','BadBranch']:
  src=INPUT/'evidence/fresh-source-w0h5n10v'/f'{name}.lean'
  shutil.copyfile(src,WORK/src.name)
  run('reject-'+name,[str(BIN/'lean'),src.name],True)
 (WORK/'BadZeroDegreeHighMean.lean').write_text('''import CriticControls
open Erdos128 Erdos128.ProfileBridge Erdos128.ProfileControls CriticE8
example : weightedMean singletonWeight (highProfile emptyGraph singletonWeight (4 / 5) 0) = 4 / 5 := by
  rw [zero_degree_high_mean]
  norm_num
''')
 run('reject-BadZeroDegreeHighMean',[str(BIN/'lean'),'BadZeroDegreeHighMean.lean'],True)
 for p,h in frozen.items():assert sha(INPUT/p)==h,p
 for mod,s in data['sources'].items():assert sha(HERE/s['input'])==s['sha256']==sha(HERE/s['copy']),mod
 data['artifact_hashes']={str(p.relative_to(WORK)):sha(p) for p in WORK.rglob('*') if p.is_file() and any(x in p.name for x in ['.olean','.ilean','.ir'])}
 data['source_hashes_stable']=True;data['completed_utc']=datetime.now(timezone.utc).isoformat();data['passed']=True;save()
 print('PASS',len(data['runs']),'steps',len(data['axioms']),'closures',flush=True)
if __name__=='__main__':main()
