#!/usr/bin/env python3
"""Critic runner. Build only frozen copied sources; reuse pinned packages only."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
WORK=next(p for p in HERE.parents if (p/'lean-controls/lean-toolchain').is_file())
BASE=WORK/'lean-controls'; INPUT=HERE/'inputs'; FRESH=HERE/'fresh'; LOG=HERE/'logs'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
FRESH.mkdir(exist_ok=True); LOG.mkdir(exist_ok=True)
assert not list(FRESH.iterdir()),'Preserve previous replay; use empty critic fresh folder.'
m=json.loads((INPUT/'builder-manifest.json').read_text())
for p,h in m['files'].items():assert sha(INPUT/p)==h,p
mods=['ComparisonEnvelope','FirstStop','StoppingCertificate','ActualStop','Recovery','RecoveryPeak','RecoveryPeakWitness']
sources={};order=[]
def visit(n):
 if n in sources:return
 p=INPUT/'fresh-replay'/Path(n.replace('.','/')+'.lean');assert p.is_file(),n;sources[n]=p
 for line in re.findall(r'^(?:public |private )?import (.+)$',p.read_text(),re.M):
  for imp in line.split():
   if imp.startswith('LeanControls.') or imp in mods:visit(imp)
 order.append(n)
visit('RecoveryPeakWitness')
assert len(sources)==38,len(sources)
for n,p in sources.items():
 out=FRESH/Path(n.replace('.','/')+'.lean');out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,out)
for n in mods:
 p=INPUT/(n+'.lean') if n.startswith('RecoveryPeak') else INPUT/'inputs'/(n+'.lean')
 assert sha(p)==sha(sources[n])
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text())
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan');lake=WORK/'.tools/elan/bin/lake'
def query(*a):return subprocess.check_output([str(lake),'env',*a],cwd=BASE,env=env,text=True).strip()
lean=Path(query('which','lean'));checker=lean.with_name('leanchecker')
paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
paths=[p for p in paths if '.lake/packages/' in p];assert paths and all('.lake/packages/' in p for p in paths)
env['LEAN_PATH']=str(FRESH)+':'+':'.join(paths);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
report={'passed':False,'builder_manifest_sha256':sha(INPUT/'builder-manifest.json'),'runner_sha256':sha(Path(__file__)),
 'scope':'38 local modules freshly built from frozen source copies; only pinned package products reused; separate kernel replay of each local module',
 'source_sha256':{n:sha(p) for n,p in sources.items()},'build_order':order,'toolchain':query('lean','--version'),
 'lean_sha256':sha(lean),'checker_sha256':sha(checker),'lean_path':env['LEAN_PATH'],
 'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),
 'package_revisions':json.loads((BASE/'lake-manifest.json').read_text())['packages'],'steps':[],'axioms':{}}
builder=json.loads((INPUT/'verification.json').read_text())
for k in ['lean_sha256','lean_toolchain_sha256','lake_manifest_sha256']:assert report[k]==builder[k],k
assert report['checker_sha256']==builder['leanchecker_sha256']
def save():(HERE/'replay-results.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args,negative=False):
 log=LOG/(label+'.log');start=time.monotonic()
 with log.open('w') as out:r=subprocess.run(list(map(str,args)),cwd=FRESH,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
 raw=log.read_text();ok=r.returncode==0
 if negative:ok=r.returncode!=0 and 'error:' in raw and any(s in raw for s in ['unsolved goals','linarith failed','Type mismatch','Application type mismatch']) and not any(s in raw.lower() for s in ['unknown identifier','unknown module','no such file'])
 report['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':r.returncode,'passed':ok,'expected':'semantic rejection' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(log)})
 save();print(label,r.returncode,ok,flush=True);assert ok,label
for n in order:
 p=FRESH/Path(n.replace('.','/')+'.lean');run('build-'+n,[lean,'--root='+str(FRESH),'-o',p.with_suffix('.olean'),p])
names=[]
for n in mods:
 raw=sources[n].read_text();ns=re.search(r'^namespace (\S+)',raw,re.M).group(1)
 names.extend(ns+'.'+t for t in re.findall(r'^theorem (\w+)',raw,re.M))
names+=['LeanControls.UncertainLag.exact_initial','LeanControls.UncertainLag.exact_ode']
(FRESH/'Audit.lean').write_text('import RecoveryPeakWitness\n'+''.join('#print axioms '+n+'\n' for n in names))
run('axiom-audit',[lean,FRESH/'Audit.lean'])
for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOG/'axiom-audit.log').read_text()):
 a={x.strip() for x in body.split(',') if x.strip()};assert a<={'propext','Classical.choice','Quot.sound'},(n,a);report['axioms'][n]=sorted(a)
assert set(report['axioms'])==set(names);save()
for n in order:run('kernel-'+n,[checker,n,'-v'])
for p in sorted((INPUT/'negative-controls').glob('*.lean')):run('reject-'+p.stem,[lean,'--root='+str(p.parent),p],True)
report['sources_unchanged']=all(sha(p)==report['source_sha256'][n] and sha(FRESH/Path(n.replace('.','/')+'.lean'))==sha(p) for n,p in sources.items())
report['inputs_unchanged']=all(sha(INPUT/p)==h for p,h in m['files'].items())
report['passed']=report['sources_unchanged'] and report['inputs_unchanged'] and all(s['passed'] for s in report['steps'])
save();print(json.dumps({'passed':report['passed'],'modules':len(sources),'axioms':len(names),'steps':len(report['steps'])}),flush=True)
