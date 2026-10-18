"""Fresh source closure, all-public axiom audit, kernel replay, and implementation mutants."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,shutil,subprocess,tempfile,time
import dev,generate_fixtures
HERE=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
EXPECTED_MANIFESTS={
 'lead-01':'9fa2ac2917bdf273c2cf4632d7da44aea08ba18a8bea8b84146eb5d2454f10ec',
 'ultra-preflight-02':'28f1ea47c3937e9046e44291372acc3d737379ac73a77b323821dc8256dda8fd'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def statements(p):
 s=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',s.replace('def admit ','def admissionFunction ').replace('admit h ','admissionFunction h ').replace('unfold admit','unfold admissionFunction').replace('[admit,','[admissionFunction,')),p
 # The legitimate function name RobotMotion.admit is not the proof escape tactic.
 assert not re.search(r'\b(sorry|axiom|native_decide|unsafe)\b',s),p
 assert not re.search(r':=\s*by\s+admit\b|\n\s*admit\s*$',s),p
 ns=re.findall(r'^namespace (\S+)',s,re.M);assert len(ns)==1,(p,ns)
 names=[]
 for line in s.splitlines():
  m=re.match(r'^\s*(.*?)\b(?:theorem|lemma)\s+([^\s{(:]+)',line)
  if m and not re.search(r'\bprivate\b',m.group(1)):names.append(ns[0]+'.'+m.group(2))
 return names

def frozen_inputs():
 rows={}
 for folder,expected in EXPECTED_MANIFESTS.items():
  root=HERE.parent.parent/folder;manifest=root/'artifact-sha256.json'
  assert sha(manifest)==expected,(folder,'manifest changed')
  data=json.loads(manifest.read_text());rows[folder]={'manifest_sha256':sha(manifest),'files':{}}
  for name,value in data['files'].items():
   assert sha(root/name)==value,(folder,name)
   rows[folder]['files'][name]=value
 assert (HERE/'Primitive.lean').read_bytes()==(HERE.parent.parent/'ultra-preflight-02/PrimitiveProbe.lean').read_bytes()
 return rows

def main():
 env,lean,dep=dev.environment();checker=str(Path(lean).with_name('leanchecker'))
 sources=dev.source_closure('Composition');sources.update(dev.source_closure('Fixtures'))
 assert len(sources)==44,len(sources)
 public={m:statements(p) for m,p in sources.items()};names=[n for xs in public.values() for n in xs]
 assert len(names)==len(set(names))
 assert (HERE/'Fixtures.lean').read_text()==generate_fixtures.render()
 logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
 manifest=json.loads((dev.BASE/'lake-manifest.json').read_text())
 report={'passed':False,'started_utc':datetime.now(timezone.utc).isoformat(),
 'scope':'All44 local modules compiled fresh from copied source. Pinned Mathlib package cache reused. Every public theorem in the local closure audited. Separate leanchecker replay for every new module and ScaledTracking. Four actual implementation/bound mutants must fail.',
 'toolchain':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),
 'lean_sha256':sha(Path(lean)),'leanchecker_sha256':sha(Path(checker)),
 'lean_toolchain_file':(dev.BASE/'lean-toolchain').read_text().strip(),
 'lake_manifest_sha256':sha(dev.BASE/'lake-manifest.json'),
 'mathlib_pinned_revision':next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib'),
 'source_paths':{m:str(p.relative_to(dev.WORK)) for m,p in sources.items()},
 'source_sha256':{m:sha(p) for m,p in sources.items()},
 'public_statements_by_module':public,'public_statement_count':len(names),
 'frozen_inputs_before':frozen_inputs(),'fixture_binding':json.loads((HERE/'fixture-binding.json').read_text()),
 'verifier_sha256':sha(Path(__file__)),'build_helper_sha256':sha(HERE/'dev.py'),
 'steps':[],'axioms':{}}
 def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
 def run(label,args,cwd,renv,negative=False,timeout=900):
  start=time.monotonic();log=logs/(label+'.log')
  with log.open('w') as out:
   proc=subprocess.run(args,cwd=cwd,env=renv,stdout=out,stderr=subprocess.STDOUT,timeout=timeout)
  ok=proc.returncode!=0 if negative else proc.returncode==0
  report['steps'].append({'label':label,'exit_code':proc.returncode,'passed':ok,
    'expected':'rejection' if negative else 'success','seconds':time.monotonic()-start,
    'log_sha256':sha(log)})
  save();print(label,proc.returncode,flush=True);assert ok,label
  return log
 save()
 with tempfile.TemporaryDirectory(prefix='fresh-',dir=HERE/'build') as tmp:
  root=Path(tmp);renv=env.copy();renv['LEAN_PATH']=str(root)+':'+dep
  renv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
  for m,p in sources.items():
   dst=root/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
   run('build-'+m,[lean,'--root='+str(root),'-o',str(dst.with_suffix('.olean')),str(dst)],root,renv)
  fixture_log=(logs/'build-Fixtures.log').read_text()
  final_results=re.findall(r'\("(frozen_[^"]+)", (true|false)\)',fixture_log)
  admission_results=re.findall(r'\("([^\"]+_admission_\d+)", (true|false), (true|false)\)',fixture_log)
  assert len(final_results)==7 and all(v=='true' for _,v in final_results),final_results
  assert len(admission_results)==52 and all(a==b for _,a,b in admission_results),admission_results
  report['lean_fixture_executions']={'seven_final_histories':final_results,'admission_transcript':admission_results,
    'final_histories_kernel_proved':True,'decide_kernel_mode':True}
  (root/'Audit.lean').write_text('import Composition\nimport Fixtures\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
  run('axiom-audit',[lean,str(root/'Audit.lean')],root,renv)
  audit=(logs/'axiom-audit.log').read_text()
  for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",audit):
   axioms={x.strip() for x in raw.split(',') if x.strip()};assert axioms<=ALLOWED,(name,axioms)
   report['axioms'][name]=sorted(axioms)
  for name in re.findall(r"'([^']+)' does not depend on any axioms",audit):report['axioms'][name]=[]
  assert set(report['axioms'])==set(names),set(names)-set(report['axioms'])
  for m in ['ScaledTracking']+dev.TARGETS:
   run('kernel-'+m,[checker,m,'-v'],root,renv)
  mutants={}
  for name in ['OmitCurrent','OmitInterior','EraseFuture','FalseUnitJerk']:
   p=HERE/'negative-controls'/(name+'.lean');dst=root/(name+'.lean');shutil.copy2(p,dst)
   log=run('reject-'+name,[lean,str(dst)],root,renv,negative=True)
   result=log.read_text()
   assert 'error:' in result and 'unknown identifier' not in result and 'unknown module' not in result and 'object file' not in result,name
   assert 'kernel' in result or 'decide' in result,name
   mutants[name]={'source_sha256':sha(p),'compile_rejected':True,'log_sha256':sha(log)}
  report['negative_controls']=mutants
 run('independent-arithmetic',['python3',str(HERE/'independent_arithmetic.py')],HERE,env)
 report['independent_arithmetic']=json.loads((HERE/'independent-arithmetic.json').read_text())
 report['source_unchanged']=all(sha(p)==report['source_sha256'][m] for m,p in sources.items())
 report['frozen_inputs_after']=frozen_inputs()
 report['pins_unchanged']=sha(dev.BASE/'lake-manifest.json')==report['lake_manifest_sha256'] and (dev.BASE/'lean-toolchain').read_text().strip()==report['lean_toolchain_file']
 report['passed']=report['source_unchanged'] and report['pins_unchanged'] and all(x['passed'] for x in report['steps'])
 report['finished_utc']=datetime.now(timezone.utc).isoformat();save()
 print(json.dumps({'passed':report['passed'],'public_statements':len(names),'local_modules':len(sources)}),flush=True)
if __name__=='__main__':main()
