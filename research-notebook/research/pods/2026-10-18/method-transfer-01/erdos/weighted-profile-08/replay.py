#!/usr/bin/env python3
"""E8 fresh-source compilation, full public axiom closures, kernel replay.

Uses the existing local Lean4.35/mathlib pin. Installs and mutates no package.
Fresh workspaces do not import development or earlier research build products.
Every attempt, including failures, is retained.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lean-controls').is_dir())
BIN=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
UPSTREAM=['Erdos128.WeightedGraph','Erdos128.CubicNeighborhood','Erdos128.OneStepSaving']
NEW=['WeightedProfiles','ProfileControls']
ALLOWED={'propext','Classical.choice','Quot.sound'}
EXPECTED={'Erdos128.WeightedGraph':'debce20bf9919c41b32f6c7ef77fd589cc6c9cb4c7b812f77562bf81f55bc9ca',
 'Erdos128.CubicNeighborhood':'50c14ea689c242868083d5bb30d20f8df320d545aaf107d4e10c61e235b6821f',
 'Erdos128.OneStepSaving':'bcb2732bd8a6b3dc762e4301fb6d59812bc58945c56c11a73cc3e411770c3553'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 evidence=HERE/'evidence';evidence.mkdir(exist_ok=True)
 work=Path(tempfile.mkdtemp(prefix='fresh-source-',dir=evidence));sources={};decls=[]
 for mod in UPSTREAM+NEW:
  rel=Path(mod.replace('.','/')).with_suffix('.lean')
  src=HERE/'upstream-source'/rel if mod in UPSTREAM else HERE/rel
  dst=work/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
  assert sha(src)==sha(dst)
  if mod in EXPECTED:assert sha(src)==EXPECTED[mod],'changed upstream source'
  text=src.read_text()
  forbidden=re.findall(r'\bsorry\b|\badmit\b|\bnative_decide\b|trustCompiler|(?m:^\s*(?:axiom|unsafe)\b)',text)
  assert not forbidden,(mod,forbidden)
  ns='Erdos128' if mod in UPSTREAM else 'Erdos128.ProfileBridge' if mod=='WeightedProfiles' else 'Erdos128.ProfileControls'
  names=re.findall(r'^(?:@\[simp\]\s+)?theorem\s+([\w]+)',text,re.M)
  decls += [ns+'.'+name for name in names]
  sources[mod]={'source':str(src.relative_to(HERE)),'copied':str(dst.relative_to(HERE)),
                'sha256':sha(src),'public_theorems':len(names),'forbidden_source_matches':forbidden}
 audit='import ProfileControls\nset_option format.width 120\nset_option pp.universes false\n'
 audit+='\n'.join('#print axioms '+n for n in decls)+'\n'
 audit+='set_option pp.universes true\n#check @Erdos128.ProfileBridge.exists_affine_profile\n'
 audit+='#check @Erdos128.ProfileBridge.mean_second_degree\n#check @Erdos128.ProfileBridge.objective_twoLevel\n'
 for n in ['Erdos128.RatProbabilityWeight','Erdos128.IsUnitProfile','Erdos128.weightedMean',
           'Erdos128.weightedDegree','Erdos128.weightedSecondDegree','Erdos128.edgeMass',
           'Erdos128.weightedObjective','Erdos128.ProfileBridge.lowProfile','Erdos128.ProfileBridge.highProfile']:
  audit+='#print '+n+'\n'
 (work/'Audit.lean').write_text(audit)
 deps=sorted(p/'.lake/build/lib/lean' for p in (ROOT/'lean-controls/.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir())
 env=os.environ.copy();env['PATH']=str(BIN)+os.pathsep+env.get('PATH','')
 env['LEAN_PATH']=os.pathsep.join(map(str,[work,*deps]))
 manifest=json.loads((ROOT/'lean-controls/lake-manifest.json').read_text())
 result={'started_utc':datetime.now(timezone.utc).isoformat(),'work':str(work.relative_to(HERE)),
  'kind':'Fresh unchanged upstream and new E8 sources under existing Lean4.35/mathlib; not a Lean4.30 replay',
  'executed_lean':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),
  'mathlib_pin':next(p for p in manifest['packages'] if p['name']=='mathlib'),
  'lean_path':env['LEAN_PATH'],'source':sources,'declarations_audited':decls,'axioms':{},'runs':[],
  'allowed_axioms':sorted(ALLOWED),'development_products_imported':False,'negative_controls':[]}
 def save():
  result['source_hashes_stable']=all(sha(HERE/s['source'])==s['sha256']==sha(HERE/s['copied']) for s in sources.values())
  (work/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 def run(label,cmd,limit=180):
  start=time.monotonic()
  try:
   done=subprocess.run(cmd,cwd=work,env=env,text=True,capture_output=True,timeout=limit)
   output=done.stdout+done.stderr;code=done.returncode
  except subprocess.TimeoutExpired as exc:
   output=str(exc.stdout or '')+'\n'+str(exc.stderr or '')+'\nTIMEOUT\n';code=124
  (work/(label+'.log')).write_text(output)
  result['runs'].append({'label':label,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'log':label+'.log'})
  save();print(label,code,flush=True);return code,output
 for mod in UPSTREAM+NEW+['Audit']:
  rel=Path(mod.replace('.','/')).with_suffix('.lean')
  code,out=run('compile-'+mod.replace('.','-'),[str(BIN/'lean'),'-o',str(rel.with_suffix('.olean')),str(rel)])
  if code:result['passed']=False;result['stopped_at']='compile '+mod;save();return 1
  if mod=='Audit':
   result['axioms']={name:[x.strip() for x in axes.split(',') if x.strip()]
                    for name,axes in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
   for name in re.findall(r"'([^']+)' does not depend on any axioms",out):result['axioms'][name]=[]
   assert set(result['axioms'])==set(decls),(set(decls)-set(result['axioms']),set(result['axioms'])-set(decls))
   assert all(set(a)<=ALLOWED for a in result['axioms'].values()),result['axioms']
 for mod in UPSTREAM+NEW+['Audit']:
  code,_=run('kernel-'+mod.replace('.','-'),[str(BIN/'leanchecker'),mod,'-v'])
  if code:result['passed']=False;result['stopped_at']='kernel '+mod;save();return 1
 negatives={
 'BadTriangle':'''import ProfileControls
open Erdos128 Erdos128.ProfileControls
example : ∃ π : Fin 3 → ℚ, IsUnitProfile π ∧ weightedMean thirds π = 1 / 2 ∧
    weightedObjective triangle thirds (fun _ => 0) π ≤ 0 := by
  have h := triangle_refutes_missing_triangle_free
  simp_all
''',
 'BadMean':'''import ProfileControls
open Erdos128 Erdos128.ProfileControls
example : weightedMean halves (fun v : Fin 2 => if v = 0 then 4 / 5 else 0) = 4 / 5 := by
  norm_num [weightedMean, halves, Fin.sum_univ_succ]
''',
 'BadNormalization':'''import ProfileControls
open Erdos128 Erdos128.ProfileControls
example : ∃ W : RatProbabilityWeight (Fin 2), W.weight = fun _ => 1 := by
  have h := two_unit_masses_not_probability
  simp_all
''',
 'BadBranch':'''import ProfileControls
open Erdos128 Erdos128.ProfileBridge Erdos128.ProfileControls
example : IsUnitProfile (lowProfile edge halves (4 / 5) 0) := by
  have h := wrong_low_branch_not_unit
  simp_all
'''}
 for name,source in negatives.items():
  (work/(name+'.lean')).write_text(source)
  code,out=run('reject-'+name,[str(BIN/'lean'),name+'.lean'],60)
  assert code!=0 and code!=124,'false control accepted or timed out'
  assert 'unsolved goals' in out and not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize',out),out
  result['negative_controls'].append({'name':name,'expected_rejection':True,'source':name+'.lean','log':'reject-'+name+'.log'})
  save()
 artifacts={str(p.relative_to(work)):sha(p) for p in sorted(work.rglob('*')) if p.is_file() and any(s in p.name for s in ['.olean','.ilean','.ir'])}
 result['build_artifact_hashes']=artifacts
 result['passed']=True;result['completed_utc']=datetime.now(timezone.utc).isoformat();save()
 print(json.dumps({'passed':True,'work':str(work),'audits':len(decls),'kernel_modules':6,'negative_controls':len(negatives)}),flush=True)
 return 0
if __name__=='__main__':sys.exit(main())
