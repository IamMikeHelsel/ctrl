"""Independent fresh-copy verifier; never writes to builder or its dependencies."""
from pathlib import Path
import os,re,json,hashlib,subprocess,time,shutil
from datetime import datetime,timezone

HERE=Path(__file__).resolve().parent
WORK=HERE.parents[5]; BUILDER=HERE.parent/'builder'; BASE=WORK/'lean-controls'
EXPECTED='740ebc266891b3f98b9ee567d19cced3c3ff187cbc091c08edfa52b276cd90fa'
PACKAGE=['Primitive','Kernel','Knots','RationalGuard','Reference','Admission','Composition','Fixtures']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_frozen():
    assert sha(BUILDER/'artifact-sha256.json')==EXPECTED
    manifest=json.loads((BUILDER/'artifact-sha256.json').read_text())
    for name,h in manifest['files'].items():assert sha(BUILDER/name)==h,name
    return manifest
frozen=check_frozen()
v=json.loads((BUILDER/'verification.json').read_text())
declared={m:WORK/p for m,p in v['source_paths'].items()}
sources={}
def visit(m):
    if m in sources:return
    p=declared[m];s=p.read_text()
    assert sha(p)==v['source_sha256'][m],m
    for line in s.splitlines():
        line=line.removeprefix('public ')
        if line.startswith('import '):
            for d in line[7:].split():
                if d in declared:visit(d)
                else:assert d.startswith(('Mathlib','Lean','Init','Std','Batteries','Qq','Aesop')),d
    sources[m]=p
visit('Composition');visit('Fixtures')
assert set(sources)==set(declared) and len(sources)==44
snapshot={m:sha(p) for m,p in sources.items()}
root=HERE/'fresh-src';root.mkdir(exist_ok=False)
logs=HERE/'logs';logs.mkdir(exist_ok=True)
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
dep=[]
for item in query('printenv','LEAN_PATH').split(':'):
    p=(BASE/item).resolve()
    if '.lake/packages/' in str(p):dep.append(str(p))
assert dep
env['LEAN_PATH']=':'.join([str(root)]+dep)
env['PATH']=str(Path(lean).parent)+os.pathsep+env['PATH']
report={'passed':False,'started_utc':datetime.now(timezone.utc).isoformat(),'builder_manifest':EXPECTED,
 'builder_manifest_files':len(frozen['files']),'local_module_count':44,'source_sha256':snapshot,
 'source_paths':{m:str(p.relative_to(WORK)) for m,p in sources.items()},'lean':lean,'checker':checker,
 'lean_sha256':sha(Path(lean)),'checker_sha256':sha(Path(checker)),
 'toolchain':query('lean','--version'),'lean_path':env['LEAN_PATH'],
 'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),'steps':[]}
(HERE/'environment.json').write_text(json.dumps({'lean':lean,'checker':checker,'env':{'ELAN_HOME':env['ELAN_HOME'],'LEAN_PATH':env['LEAN_PATH'],'PATH':env['PATH']},'root':str(root)},indent=2)+'\n')
def save():(HERE/'replay-results.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args,negative=False):
    t=time.monotonic();log=logs/(label+'.log')
    with log.open('w') as out:r=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
    success=(r.returncode!=0) if negative else (r.returncode==0)
    report['steps'].append({'label':label,'exit_code':r.returncode,'passed':success,'seconds':time.monotonic()-t,'log_sha256':sha(log)})
    save();print(label,r.returncode,flush=True)
    assert success,label
    return log.read_text()
save()
theorems={};other={}
for m,p in sources.items():
    dst=root/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
    s=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
    assert not re.search(r'\b(sorry|axiom|native_decide|unsafe)\b',s),m
    assert not re.search(r':=\s*by\s+admit\b|\n\s*admit\s*$',s),m
    ns=re.findall(r'^namespace (\S+)',s,re.M);assert len(ns)==1,(m,ns)
    theorems[m]=[];other[m]=[]
    for line in s.splitlines():
        d=re.match(r'^\s*(.*?)\b(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s{(:]+)',line)
        if d and not re.search(r'\bprivate\b',d[1]):
            (theorems if d[2] in ('lemma','theorem') else other)[m].append(ns[0]+'.'+d[3])
    run('build-'+m,[lean,'--root='+str(root),'-o',str(dst.with_suffix('.olean')),str(dst)])
report['public_theorems_by_module']=theorems;report['other_named_declarations_by_module']=other
report['public_theorems_total']=sum(map(len,theorems.values()))
report['package_theorems']=sum(len(theorems[m]) for m in PACKAGE)
report['inherited_theorems']=sum(len(theorems[m]) for m in sources if m not in PACKAGE)
assert report['public_theorems_total']==660 and report['package_theorems']==106
names=[n for rows in [theorems,other] for ns in rows.values() for n in ns]
assert len(names)==len(set(names))
(root/'ReviewAudit.lean').write_text('import Composition\nimport Fixtures\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
audit=run('axiom-audit',[lean,str(root/'ReviewAudit.lean')])
axioms={}
for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",audit):
    a={x.strip() for x in raw.split(',') if x.strip()};assert a<={'propext','Classical.choice','Quot.sound'},(name,a)
    axioms[name]=sorted(a)
for name in re.findall(r"'([^']+)' does not depend on any axioms",audit):axioms[name]=[]
assert set(axioms)==set(names),set(names)-set(axioms)
report['axioms']=axioms
for m in ['ScaledTracking']+PACKAGE:run('kernel-'+m,[checker,m,'-v'])
for name in ['OmitCurrent','OmitInterior','EraseFuture','FalseUnitJerk']:
    p=BUILDER/'negative-controls'/(name+'.lean');dst=root/(name+'.lean');shutil.copy2(p,dst)
    text=run('negative-'+name,[lean,str(dst)],True)
    assert 'error:' in text and ('decide' in text or 'kernel' in text)
    assert not any(x in text for x in ['unknown identifier','unknown module','object file']),name
flog=(logs/'build-Fixtures.log').read_text()
finals=re.findall(r'\("(frozen_[^"]+)", (true|false)\)',flog)
admissions=re.findall(r'\("([^\"]+_admission_\d+)", (true|false), (true|false)\)',flog)
assert len(finals)==7 and all(x=='true' for _,x in finals)
assert len(admissions)==52 and all(a==b for _,a,b in admissions)
report['fixture_execution']={'final_histories':finals,'admission_evaluations':admissions}
assert check_frozen()==frozen
assert all(sha(p)==snapshot[m] and sha(root/(m.replace('.','/')+'.lean'))==snapshot[m] for m,p in sources.items())
assert sha(BASE/'lake-manifest.json')==report['lake_manifest_sha256']
report['frozen_files_preserved']=True;report['source_copies_match']=True
report['finished_utc']=datetime.now(timezone.utc).isoformat();report['passed']=True;save()
print(json.dumps({'passed':True,'theorems':report['public_theorems_total'],'package':report['package_theorems'],'inherited':report['inherited_theorems'],'other_declarations':sum(map(len,other.values()))}),flush=True)
