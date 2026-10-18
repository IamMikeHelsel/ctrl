#!/usr/bin/env python3
"""Fresh copied-source compile, complete public axiom audit, separate kernels, false claims.
No development products or prior research products enter LEAN_PATH.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
H=Path(__file__).resolve().parent;ROOT=next(p for p in H.parents if (p/'lean-controls').is_dir())
BIN=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
MODULES=['Erdos128.WeightedGraph','Erdos128.CubicNeighborhood','Erdos128.OneStepSaving','WeightedProfiles','SquareCertificate','RationalIntervals','SelectorSemantics','CheckedTree','UniversalSelector','SelectorControls']
ALLOWED={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 work=Path(tempfile.mkdtemp(prefix='fresh-source-',dir=H/'evidence'));sources={};decls=[]
 provenance=json.loads((H/'INPUTS.json').read_text());expected={d['module']:d['sha256'] for d in provenance['unchanged_dependencies']}
 for mod in MODULES:
  rel=Path(mod.replace('.','/')).with_suffix('.lean');src=H/rel;dst=work/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
  assert sha(src)==sha(dst)
  if mod in expected:assert sha(src)==expected[mod]
  txt=src.read_text();bad=re.findall(r'\bsorry\b|\badmit\b|\bnative_decide\b|trustCompiler|(?m:^\s*(?:axiom|unsafe)\b)',txt);assert not bad,(mod,bad)
  stack=[];names=[]
  for line in txt.splitlines():
   ns=re.match(r'^namespace (\S+)',line)
   if ns:stack.append(ns.group(1))
   end=re.match(r'^end (\S+)',line)
   if end and stack and end.group(1)==stack[-1]:stack.pop()
   theorem=re.match(r'^(?:@\[[^]]*\]\s+)?(?:theorem|lemma)\s+(\w+)',line)
   if theorem:names.append('.'.join(stack+[theorem.group(1)]))
  decls+=names;sources[mod]={'source':str(rel),'sha256':sha(src),'public_theorems':len(names),'forbidden_source_matches':bad}
 audit='import SelectorControls\nset_option format.width 160\nset_option pp.universes false\n'
 audit+='\n'.join('#print axioms '+n for n in decls)+'\nset_option pp.universes true\n'
 for n in ['E10.universal_selector','E10.Expr.sound','E10.moment_sound','E10.split_c','E10.split_j','E10.completion_antitone','E10.Controls.wrong_target_counterexample','E10.Controls.matched_slope_needed']:
  audit+='#check @'+n+'\n'
 for n in ['E10.Selected','E10.R','E10.I','E10.completion','E10.Q','Erdos128.FiniteProfileBridge.lowCertificate','Erdos128.FiniteProfileBridge.highCertificate']:
  audit+='#print '+n+'\n'
 (work/'Audit.lean').write_text(audit)
 deps=sorted(p/'.lake/build/lib/lean' for p in (ROOT/'lean-controls/.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir())
 env=os.environ.copy();env['PATH']=str(BIN)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join(map(str,[work,*deps]))
 result={'started_utc':datetime.now(timezone.utc).isoformat(),'work':str(work.relative_to(H)),'executed_lean':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),'executed_mathlib':provenance['executed_mathlib'],'source':sources,'declarations_audited':decls,'allowed_axioms':sorted(ALLOWED),'axioms':{},'runs':[],'negative_controls':[],'development_products_imported':False,'lean_path':env['LEAN_PATH']}
 def save():
  result['source_hashes_stable']=all(sha(H/s['source'])==s['sha256']==sha(work/s['source']) for s in sources.values());(work/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 def run(label,cmd,limit=300):
  start=time.monotonic()
  try:
   p=subprocess.run(cmd,cwd=work,env=env,capture_output=True,text=True,timeout=limit);out=p.stdout+p.stderr;code=p.returncode
  except subprocess.TimeoutExpired as e:out=str(e.stdout or '')+'\n'+str(e.stderr or '')+'\nTIMEOUT\n';code=124
  (work/(label+'.log')).write_text(out);result['runs'].append({'label':label,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'log':label+'.log'});save();print(label,code,flush=True);return code,out
 for mod in MODULES+['Audit']:
  rel=Path(mod.replace('.','/')).with_suffix('.lean');code,out=run('compile-'+mod.replace('.','-'),[str(BIN/'lean'),'-o',str(rel.with_suffix('.olean')),str(rel)])
  if code:result['passed']=False;result['stopped_at']='compile '+mod;save();return 1
  if mod=='Audit':
   result['axioms']={n:[s.strip() for s in a.split(',') if s.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
   for n in re.findall(r"'([^']+)' does not depend on any axioms",out):result['axioms'][n]=[]
   assert set(result['axioms'])==set(decls),(set(decls)-set(result['axioms']),set(result['axioms'])-set(decls))
   assert all(set(a)<=ALLOWED for a in result['axioms'].values())
 for mod in MODULES+['Audit']:
  code,out=run('kernel-'+mod.replace('.','-'),[str(BIN/'leanchecker'),mod,'-v'],600 if mod=='CheckedTree' else 300)
  if code:result['passed']=False;result['stopped_at']='kernel '+mod;save();return 1
 prefix='import SelectorControls\nopen E10 E10.Controls Erdos128.FiniteProfileBridge\n'
 negatives={
 'MissingChild':prefix+'example : Mem (22/25:ℚ) (767/1000,4/5) := by\n norm_num [Mem]\n',
 'WrongBoundary':prefix+'example : (4/5:ℚ)<4/5 ∨ (4/5:ℚ)<4/5 := by\n norm_num\n',
 'FalseSquareBound':prefix+'example : (sq (-1,2)).1 = 1 := by\n norm_num [sq]\n',
 'WrongReciprocalOrder':prefix+'example : Mem (1/(2:ℚ)) (1,1/2) := by\n norm_num [Mem]\n',
 'WrongSlope':prefix+'example : highCertificate (1/(2*cm)) jm R (Expr.slope cm jm 0) ≤ 0 := by\n have h := matched_slope_needed.2.2.1\n simp_all only [not_le_of_gt h]\n',
 'WrongTarget':prefix+'example : AtTarget r0 c0 j0 := by\n have h := wrong_target_counterexample.2.2.2.2\n simp_all\n',
 'VariableSlopeCancellation':prefix+'example : ((-1:ℚ)*(1/4-1/2)+(1:ℚ)*(3/4-1/2))/2 = 0 := by\n norm_num\n'}
 for name,src in negatives.items():
  (work/(name+'.lean')).write_text(src);code,out=run('reject-'+name,[str(BIN/'lean'),name+'.lean'],60)
  assert code!=0 and code!=124,(name,'accepted or timeout')
  assert 'unsolved goals' in out and not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize|Type mismatch',out),out
  result['negative_controls'].append({'name':name,'expected_rejection':True,'source':name+'.lean','log':'reject-'+name+'.log'});save()
 result['build_artifact_hashes']={str(p.relative_to(work)):sha(p) for p in sorted(work.rglob('*')) if p.is_file() and any(x in p.name for x in ['.olean','.ilean','.ir'])}
 result['passed']=True;result['completed_utc']=datetime.now(timezone.utc).isoformat();save();print(json.dumps({'passed':True,'work':str(work),'audits':len(decls),'kernel_modules':len(MODULES)+1,'negative_controls':len(negatives)}),flush=True);return 0
if __name__=='__main__':sys.exit(main())
