#!/usr/bin/env python3
"""Independent C3 replay from frozen source copies; packages only from pin."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent;WORK=next(p for p in HERE.parents if (p/'lean-controls/lean-toolchain').is_file());BASE=WORK/'lean-controls';INPUT=HERE/'inputs';FRESH=HERE/'fresh';LOG=HERE/'logs'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
FRESH.mkdir(exist_ok=True);LOG.mkdir(exist_ok=True);assert not list(FRESH.iterdir())
m=json.loads((INPUT/'builder-manifest.json').read_text())
for p,h in m['files'].items():assert sha(INPUT/p)==h,p
mods=['DigitalHold','AdaptiveAdmission','AdaptiveWitness','AdmissionInterface'];sources={n:INPUT/('inputs' if n=='DigitalHold' else '')/(n+'.lean') for n in mods}
imports={n:re.findall(r'^(?:public |private )?import (\S+)',p.read_text(),re.M) for n,p in sources.items()}
assert all(i.startswith('Mathlib.') or i in mods for v in imports.values() for i in v)
order=[]
def visit(n):
 if n in order:return
 for i in imports[n]:
  if i in mods:visit(i)
 order.append(n)
visit('AdmissionInterface');assert order==mods
assert sha(sources['DigitalHold'])=='aa91b649affc0906c79dd7a017b34d6f729d1c16f50117ab87daaa1ed2fadc03'
for n,p in sources.items():
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text())
 shutil.copy2(p,FRESH/p.name)
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan');lake=WORK/'.tools/elan/bin/lake'
def query(*a):return subprocess.check_output([str(lake),'env',*a],cwd=BASE,env=env,text=True).strip()
lean=Path(query('which','lean'));checker=lean.with_name('leanchecker')
paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')];paths=[p for p in paths if '.lake/packages/' in p];assert paths
env['LEAN_PATH']=str(FRESH)+':'+':'.join(paths);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
r={'passed':False,'builder_manifest_sha256':sha(INPUT/'builder-manifest.json'),'runner_sha256':sha(Path(__file__)),'scope':'Four local modules rebuilt from frozen source and separately kernel checked. Pinned external package products reused; no local proof cache imported.',
 'source_sha256':{n:sha(p) for n,p in sources.items()},'local_import_graph':imports,'build_order':order,'toolchain':query('lean','--version'),'lean_sha256':sha(lean),'checker_sha256':sha(checker),'lean_path':env['LEAN_PATH'],'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),'package_revisions':json.loads((BASE/'lake-manifest.json').read_text())['packages'],'steps':[],'axioms':{}}
b=json.loads((INPUT/'verification.json').read_text())
for k in ['toolchain','lean_sha256','lean_toolchain_sha256','lake_manifest_sha256']:assert r[k]==b[k],k
assert r['checker_sha256']==b['leanchecker_sha256']
def save():(HERE/'replay-results.json').write_text(json.dumps(r,indent=2)+'\n')
def run(label,args,neg=False):
 log=LOG/(label+'.log');start=time.monotonic()
 with log.open('w') as out:p=subprocess.run(list(map(str,args)),cwd=FRESH,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
 text=log.read_text();ok=p.returncode==0
 if neg:ok=p.returncode!=0 and 'error:' in text and any(s in text for s in ['unsolved goals','linarith failed','Type mismatch','Application type mismatch']) and not any(s in text.lower() for s in ['unknown identifier','unknown module','no such file'])
 r['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':p.returncode,'passed':ok,'expected':'semantic rejection' if neg else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(log)})
 save();print(label,p.returncode,ok,flush=True);assert ok,label
names=[]
for n in order:
 p=FRESH/(n+'.lean');run('build-'+n,[lean,'--root='+str(FRESH),'-o',p.with_suffix('.olean'),p]);raw=p.read_text();ns=re.search(r'^namespace (\S+)',raw,re.M).group(1);names.extend(ns+'.'+t for t in re.findall(r'^theorem (\w+)',raw,re.M))
(FRESH/'Audit.lean').write_text('import AdmissionInterface\n'+''.join('#print axioms '+n+'\n' for n in names));run('axiom-audit',[lean,FRESH/'Audit.lean'])
for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOG/'axiom-audit.log').read_text()):
 a={s.strip() for s in body.split(',') if s.strip()};assert a<={'propext','Classical.choice','Quot.sound'};r['axioms'][n]=sorted(a)
assert set(r['axioms'])==set(names);save()
for n in order:run('kernel-'+n,[checker,n,'-v'])
for p in sorted((INPUT/'negative-controls').glob('*.lean')):run('reject-'+p.stem,[lean,'--root='+str(p.parent),p],True)
r['source_unchanged']=all(sha(p)==r['source_sha256'][n] and sha(FRESH/(n+'.lean'))==sha(p) for n,p in sources.items());r['inputs_unchanged']=all(sha(INPUT/p)==h for p,h in m['files'].items());r['passed']=r['source_unchanged'] and r['inputs_unchanged'] and all(s['passed'] for s in r['steps']);save();print(json.dumps({'passed':r['passed'],'steps':len(r['steps']),'axioms':len(r['axioms'])}),flush=True)
