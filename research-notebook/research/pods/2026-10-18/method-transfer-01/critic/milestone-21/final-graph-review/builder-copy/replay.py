#!/usr/bin/env python3
"""Fresh copied-source compile, complete public axiom audit, separate kernels, false claims.
No development products or prior research products enter LEAN_PATH.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
H=Path(__file__).resolve().parent;ROOT=next(p for p in H.parents if (p/'lean-controls').is_dir())
BIN=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
MODULES=json.loads((H/'complete-closure.json').read_text())['order']
ALLOWED={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 resume = len(sys.argv)==3 and sys.argv[1]=='--resume-audit'
 work=(H/sys.argv[2]).resolve() if resume else Path(tempfile.mkdtemp(prefix='fresh-source-',dir=H/'evidence'))
 previous=None
 if resume:
  assert work.is_relative_to((H/'evidence').resolve())
  previous=json.loads((work/'verification.json').read_text())
  assert previous.get('stopped_at')=='compile Audit'
  assert all(any(r['label']=='compile-'+m.replace('.','-') and r['exit']==0 for r in previous['runs']) for m in MODULES)
  for name in ['Audit.lean','compile-Audit.log','verification.json']:
   shutil.copyfile(work/name,work/(name+'.before-parser-repair'))
 sources={};decls=[]
 provenance=json.loads((H/'INPUTS.json').read_text());expected={m:d['sha256'] for m,d in provenance['unchanged_inherited_modules'].items()}
 for mod in MODULES:
  rel=Path(mod.replace('.','/')).with_suffix('.lean');src=H/rel;dst=work/rel;dst.parent.mkdir(parents=True,exist_ok=True)
  if resume:assert sha(src)==sha(dst)==previous['source'][mod]['sha256']
  shutil.copyfile(src,dst)
  assert sha(src)==sha(dst)
  if mod in expected:assert sha(src)==expected[mod]
  txt=src.read_text();bad=re.findall(r'\bsorry\b|\badmit\b|\bnative_decide\b|trustCompiler|(?m:^\s*(?:axiom|unsafe)\s+[A-Za-z_])',txt);assert not bad,(mod,bad)
  stack=[];names=[]
  for line in txt.splitlines():
   ns=re.match(r'^namespace (\S+)',line)
   if ns:stack.append(ns.group(1))
   end=re.match(r'^end (\S+)',line)
   if end and stack and end.group(1)==stack[-1]:stack.pop()
   theorem=re.match(r"^(?:@\[[^]]*\]\s+)?(?:theorem|lemma)\s+([\w']+)",line)
   if theorem:names.append('.'.join(stack+[theorem.group(1)]))
  decls+=names;sources[mod]={'source':str(rel),'sha256':sha(src),'public_theorems':len(names),'forbidden_source_matches':bad}
 assert len(decls)==len(set(decls)), 'duplicate parsed declaration names'
 audit='import FinalControls\nset_option format.width 160\nset_option pp.universes false\n'
 audit+='\n'.join('#print axioms '+n for n in decls)+'\nset_option pp.universes true\n'
 for n in ['Erdos128.FinalGraph.sparse_half_251_10000','Erdos128.FinalGraph.fractional_251_10000_all_orders','Erdos128.FinalGraph.fractional_of_oriented_cut_even','Erdos128.FinalGraph.actual_cut_budget','Erdos128.FinalGraph.actual_completion_scale','Erdos128.FinalControls.explicit_odd_cut_endpoint','Erdos128.FinalControls.explicit_even_cut_endpoint']:
  audit+='#check @'+n+'\n'
 for n in ['Erdos128.CompletionBridge.BCLEventual','Erdos128.BCLCutCertificate','Erdos128.HasSparseHalf','Erdos128.HasNormalizedFractionalHalfBoundQ','E10.R','E10.I']:
  audit+='#print '+n+'\n'
 (work/'Audit.lean').write_text(audit)
 deps=sorted(p/'.lake/build/lib/lean' for p in (ROOT/'lean-controls/.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir())
 env=os.environ.copy();env['PATH']=str(BIN)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join(map(str,[work,*deps]))
 result={'started_utc':datetime.now(timezone.utc).isoformat(),'work':str(work.relative_to(H)),'executed_lean':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),'executed_mathlib':provenance['executed_mathlib'],'source':sources,'declarations_audited':decls,'allowed_axioms':sorted(ALLOWED),'axioms':{},'runs':[],'negative_controls':[],'development_products_imported':False,'lean_path':env['LEAN_PATH']}
 if resume:
  result['runs']=previous['runs']
  result['audit_parser_repair']={'kind':'Declaration names containing apostrophes; only Audit source regenerated. All 34 proof modules compiled from fresh copied source before this repair.','prior_verification':'verification.json.before-parser-repair'}
 def save():
  result['source_hashes_stable']=all(sha(H/s['source'])==s['sha256']==sha(work/s['source']) for s in sources.values());(work/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 def run(label,cmd,limit=300):
  start=time.monotonic()
  try:
   p=subprocess.run(cmd,cwd=work,env=env,capture_output=True,text=True,timeout=limit);out=p.stdout+p.stderr;code=p.returncode
  except subprocess.TimeoutExpired as e:out=str(e.stdout or '')+'\n'+str(e.stderr or '')+'\nTIMEOUT\n';code=124
  (work/(label+'.log')).write_text(out);result['runs'].append({'label':label,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'log':label+'.log'});save();print(label,code,flush=True);return code,out
 for mod in (['Audit'] if resume else MODULES+['Audit']):
  rel=Path(mod.replace('.','/')).with_suffix('.lean');code,out=run('compile-'+mod.replace('.','-'),[str(BIN/'lean'),'-o',str(rel.with_suffix('.olean')),str(rel)])
  if code:result['passed']=False;result['stopped_at']='compile '+mod;save();return 1
  if mod=='Audit':
   result['axioms']={n:[s.strip() for s in a.split(',') if s.strip()] for n,a in re.findall(r"'(.+)' depends on axioms: \[([^]]*)\]",out)}
   for n in re.findall(r"'(.+)' does not depend on any axioms",out):result['axioms'][n]=[]
   assert set(result['axioms'])==set(decls),(set(decls)-set(result['axioms']),set(result['axioms'])-set(decls))
   assert all(set(a)<=ALLOWED for a in result['axioms'].values())
 # Separate kernel checks run sequentially. Each check reads the fresh closure only.
 for mod in MODULES+['Audit']:
  code,out=run('kernel-'+mod.replace('.','-'),[str(BIN/'leanchecker'),mod,'-v'],600 if mod=='CheckedTree' else 300)
  if code:result['passed']=False;result['stopped_at']='kernel '+mod;save();return 1
 prefix='import FinalControls\nopen scoped BigOperators\nopen Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge\n'
 negatives={
 'MissingOrderSquare':prefix+'example : edgeCost FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ))) = normalizedEdgeCostQ FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ))) := by\n have h := Erdos128.FinalControls.missing_order_square_control\n simp_all\n',
 'DirectedEdgeDoubleCount':prefix+'example : (∑ u : Fin 6, ∑ v : Fin 6, if FiniteProfileControls.oneEdge.Adj u v then FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ)) u * FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ)) v else 0) = 9/25 := by\n rw [Erdos128.FinalControls.directed_edge_count_control]\n norm_num\n',
 'CeilRounding':prefix+'example : ∃ S : Finset (Fin 5), S.card=3 ∧ (edgeCountOn Erdos128.FinalControls.cycle5 S:ℚ)≤E10.R*25 := by\n have h := Erdos128.FinalControls.odd_ceil_impossible\n simp_all\n',
 'BalancedMoment':prefix+'example : (1/2:ℚ)<sideMass Erdos128.FinalControls.balancedCut := by\n rw [Erdos128.FinalControls.balanced_parameters.2.1]\n norm_num\n',
 'WrongHomogeneity':prefix+'example : completionEnvelope (4:ℚ) 5 = 10*E10.completion (5/6) := by\n norm_num [completionEnvelope,E10.completion,E10.Q,E10.xval]\n',
 'EmptyPositiveDenominator':prefix+'example : (0:ℚ)<(Fintype.card (Fin 0):ℚ)^2 := by\n norm_num\n',
 'WrongSideScale':prefix+'example : sideMass FiniteProfileControls.cut * weightedObjective FiniteProfileControls.cut.largeGraph FiniteProfileControls.cut.uniformLargeWeight (fun _ => 0) (fun _ => (3/5:ℚ)) = normalizedEdgeCostQ FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ))) := by\n have h := FiniteProfileControls.wrong_cost_scale.2\n simp_all\n',
 'QualifiedFalseSquare':prefix+'example : (E10.sq (-1,2)).1=1 := by\n norm_num [E10.sq]\n'}
 for name,src in negatives.items():
  (work/(name+'.lean')).write_text(src);code,out=run('reject-'+name,[str(BIN/'lean'),name+'.lean'],60)
  assert code!=0 and code!=124,(name,'accepted or timeout')
  assert 'unsolved goals' in out and not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize|Type mismatch|Ambiguous term|\bsorry\b|sorryAx',out),out
  result['negative_controls'].append({'name':name,'expected_rejection':True,'source':name+'.lean','log':'reject-'+name+'.log'});save()
 result['build_artifact_hashes']={str(p.relative_to(work)):sha(p) for p in sorted(work.rglob('*')) if p.is_file() and any(x in p.name for x in ['.olean','.ilean','.ir'])}
 result['passed']=True;result['completed_utc']=datetime.now(timezone.utc).isoformat();save();print(json.dumps({'passed':True,'work':str(work),'audits':len(decls),'kernel_modules':len(MODULES)+1,'negative_controls':len(negatives)}),flush=True);return 0
if __name__=='__main__':sys.exit(main())
