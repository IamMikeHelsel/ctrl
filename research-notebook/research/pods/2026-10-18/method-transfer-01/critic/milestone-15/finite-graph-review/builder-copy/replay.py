#!/usr/bin/env python3
"""E9 fresh-source compilation, full public axiom closures, kernel replay.

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
UPSTREAM=['Erdos128.GraphBasics','Erdos128.GraphRational','Erdos128.ExternalInputs','Erdos128.LowDensityGraph','Erdos128.WeightedGraph','Erdos128.CubicNeighborhood','Erdos128.OneStepSaving']
NEW=['WeightedProfiles','CutHelpers','SquareCertificate','FiniteGraphBridge','FiniteControls']
ALLOWED={'propext','Classical.choice','Quot.sound'}
EXPECTED={'Erdos128.GraphBasics': 'ddf949f92df8c1b69140d43b8f03337f1fa6300ef761ce9572aabc66d278bce8', 'Erdos128.GraphRational': '036ba4bb58577cbae5dbbab378e5e1b4f7f1a1c6ec25592bebc81d76bc4e7d6c', 'Erdos128.ExternalInputs': '9ab031281141a1b22da1ac22b5259ad7490f79091b828c3f658b74ac04a5ef10', 'Erdos128.LowDensityGraph': '52c0f98b72ab76bc017e179efdc7d103dab742bee993d6ec6928b30b8b91548c', 'Erdos128.WeightedGraph': 'debce20bf9919c41b32f6c7ef77fd589cc6c9cb4c7b812f77562bf81f55bc9ca', 'Erdos128.CubicNeighborhood': '50c14ea689c242868083d5bb30d20f8df320d545aaf107d4e10c61e235b6821f', 'Erdos128.OneStepSaving': 'bcb2732bd8a6b3dc762e4301fb6d59812bc58945c56c11a73cc3e411770c3553'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 evidence=HERE/'evidence';evidence.mkdir(exist_ok=True)
 work=Path(tempfile.mkdtemp(prefix='fresh-source-',dir=evidence));sources={};decls=[]
 for mod in UPSTREAM+NEW:
  rel=Path(mod.replace('.','/')).with_suffix('.lean')
  src=HERE/'upstream-original'/rel if mod in UPSTREAM else HERE/rel
  dst=work/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
  assert sha(src)==sha(dst)
  if mod in EXPECTED:assert sha(src)==EXPECTED[mod],'changed upstream source'
  if mod=='WeightedProfiles':assert sha(src)=='31e89a547ef3fa040a08de08956fc79a1ba25a4b101bc9c88414ccb349b8decd','changed accepted E8 source'
  text=src.read_text()
  forbidden=re.findall(r'\bsorry\b|\badmit\b|\bnative_decide\b|trustCompiler|(?m:^\s*(?:axiom|unsafe)\b)',text)
  assert not forbidden,(mod,forbidden)
  ns='Erdos128' if mod in UPSTREAM or mod=='CutHelpers' else 'Erdos128.ProfileBridge' if mod=='WeightedProfiles' else 'Erdos128.FiniteProfileControls' if mod=='FiniteControls' else 'Erdos128.FiniteProfileBridge'
  names=[]
  for line in text.splitlines():
   if line=='namespace OrientedBCLCut':ns='Erdos128.OrientedBCLCut'
   if line=='end OrientedBCLCut':ns='Erdos128'
   match=re.match(r'^(?:@\[[^]]*\]\s+)?(?:theorem|lemma)\s+([\w]+)',line)
   if match:names.append(ns+'.'+match.group(1))
  decls += names
  sources[mod]={'source':str(src.relative_to(HERE)),'copied':str(dst.relative_to(HERE)),
                'sha256':sha(src),'public_theorems':len(names),'forbidden_source_matches':forbidden}
 audit='import FiniteControls\nset_option format.width 120\nset_option pp.universes false\n'
 audit+='\n'.join('#print axioms '+n for n in decls)+'\n'
 audit+='set_option pp.universes true\n#check @Erdos128.FiniteProfileBridge.half_from_squared_certificates\n'
 for n in ['Erdos128.FiniteProfileBridge.normalized_certificates','Erdos128.FiniteProfileBridge.normalized_cost_extension',
           'Erdos128.FiniteProfileBridge.mass_extension','Erdos128.OrientedBCLCut.isFractionalHalf_extendLarge',
           'Erdos128.OrientedBCLCut.largeGraph_cliqueFree','Erdos128.ProfileBridge.exists_affine_profile']:
  audit+='#check @'+n+'\n'
 for n in ['Erdos128.OrientedBCLCut','Erdos128.IsFractionalHalf','Erdos128.normalizedEdgeCostQ',
           'Erdos128.HasNormalizedFractionalHalfBoundQ','Erdos128.FiniteProfileBridge.sideMass',
           'Erdos128.FiniteProfileBridge.sideEdges','Erdos128.FiniteProfileBridge.lowCertificate',
           'Erdos128.FiniteProfileBridge.highCertificate']:
  audit+='#print '+n+'\n'
 (work/'Audit.lean').write_text(audit)
 deps=sorted(p/'.lake/build/lib/lean' for p in (ROOT/'lean-controls/.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir())
 env=os.environ.copy();env['PATH']=str(BIN)+os.pathsep+env.get('PATH','')
 env['LEAN_PATH']=os.pathsep.join(map(str,[work,*deps]))
 manifest=json.loads((ROOT/'lean-controls/lake-manifest.json').read_text())
 result={'started_utc':datetime.now(timezone.utc).isoformat(),'work':str(work.relative_to(HERE)),
  'kind':'Fresh unchanged seven-module upstream closure, unchanged E8 source, attributed extracted/ported CutHelpers and new E9 sources under existing Lean4.35/mathlib; not a Lean4.30 replay',
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
 negatives={'BadCostScale': 'import FiniteControls\nopen Erdos128 Erdos128.FiniteProfileBridge Erdos128.FiniteProfileControls\nexample : sideMass cut * weightedObjective cut.largeGraph cut.uniformLargeWeight (fun _ => 0)\n  (fun _ => (3 / 5 : ℚ)) = normalizedEdgeCostQ oneEdge (cut.extendLarge (fun _ => (3 / 5 : ℚ))) := by\n  have h := wrong_cost_scale.2\n  simp_all\n', 'BadMass': 'import FiniteControls\nopen Erdos128 Erdos128.FiniteProfileControls\nexample : IsFractionalHalf (cut.extendLarge (fun _ => (1 / 2 : ℚ))) := by\n  have h := wrong_mass.2\n  simp_all\n', 'BadSlope': 'import FiniteControls\nopen Erdos128 Erdos128.FiniteProfileBridge Erdos128.FiniteProfileControls\nexample : (5 / 6 : ℚ) ^ 2 * (-1 / 15) * ((1 / 6) / (5 / 6) - 2 * ((1 / 36) / (5 / 6) ^ 2)) =\n  (-1 / 15) * ((1 / 6) - meanDegree (5 / 6) (1 / 36)) := by\n  norm_num [meanDegree]\n', 'BadBalanced': 'import FiniteControls\nexample : (1 / (2 * (1 / 2 : ℚ))) < 1 := by\n  norm_num\n'}
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
 print(json.dumps({'passed':True,'work':str(work),'audits':len(decls),'kernel_modules':len(UPSTREAM+NEW)+1,'negative_controls':len(negatives)}),flush=True)
 return 0
if __name__=='__main__':sys.exit(main())
