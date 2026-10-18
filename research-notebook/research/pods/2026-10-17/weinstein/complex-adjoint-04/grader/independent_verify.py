"""Independent copied-source check of the actual complex-adjoint construction."""
from pathlib import Path
import hashlib, json, os, re, subprocess, tempfile, time

G=Path(__file__).resolve().parent
B=G.parent/'builder'
P=G.parent.parent/'clifford-contraction-03/builder'
ROOT=G.parents[5]
BASE=ROOT/'lean-controls'
EXPECTED='c498ef42bd3d8c428a0dcab1c34d4ca1eb41e419d57a47f00fdb6eca18cb7e0e'
PREVIOUS='a283b2848de505c7565eb768e35215d9330f2eedfc015d51876fb29784aaf085'
DEPS=['CliffordModel','ContractionAlgebra','CliffordContraction','CliffordControls']
NEW=['ComplexAdjoint','AdjointControls','ComplexContraction']
MODULES=DEPS+NEW
NS={m:('GUContraction' if m=='ContractionAlgebra' else 'GUClifford') for m in DEPS}
NS.update({m:'GUComplex' for m in NEW})
SOURCES={m:(P if m in DEPS else B)/(m+'.lean') for m in MODULES}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def check_manifest(folder, expected, count):
    assert digest(folder/'SHA256SUMS')==expected
    entries={}
    for row in (folder/'SHA256SUMS').read_text().splitlines():
        h,n=row.split('  ',1)
        assert digest(folder/n)==h,n
        entries[n]=h
    assert len(entries)==count
    entries['SHA256SUMS']=expected
    return entries

def state():
    result={'gate04':check_manifest(B,EXPECTED,35),'gate03':check_manifest(P,PREVIOUS,34)}
    ledger=json.loads((B/'source-ledger.json').read_text())
    result['mathlib_sources']={}
    for n,h in ledger['mathlib_source_sha256'].items():
        actual=digest(BASE/'.lake/packages/mathlib'/n)
        assert actual==h,n
        result['mathlib_sources'][n]=actual
    return result

(G/'logs').mkdir(exist_ok=True)
(G/'cache').mkdir(exist_ok=True)
before=state()
(G/'hashes-before.json').write_text(json.dumps(before,indent=2)+'\n')
env=os.environ.copy();env['ELAN_HOME']=str(ROOT/'.tools/elan')
lake=str(ROOT/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=BASE,env=env,text=True).strip()
deps=[str((BASE/p).resolve()) for p in paths.split(':')]
env['PATH']=str(Path(lean).parent)+':'+env['PATH']
version=subprocess.check_output([lean,'--version'],env=env,text=True).strip()
assert 'version 4.35.0,' in version
revision=next(p['rev'] for p in json.loads((BASE/'lake-manifest.json').read_text())['packages'] if p['name']=='mathlib')
assert revision=='56a005855ea17e0b0958f73ec801ae140b0a1679'
steps=[]

def run(label,args,work,success=True):
    start=time.monotonic()
    p=subprocess.run(args,cwd=work,env=env,text=True,capture_output=True,timeout=300)
    out=p.stdout+p.stderr
    (G/'logs'/(label+'.log')).write_text(out)
    rec={'label':label,'command':args,'exit':p.returncode,'seconds':round(time.monotonic()-start,3)}
    steps.append(rec)
    print(json.dumps({k:v for k,v in rec.items() if k!='command'}),flush=True)
    assert (p.returncode==0)==success,out[-12000:]
    return out

pattern=r'^(?:theorem|lemma|def|abbrev|instance|structure)\s+([^\s(:]+)'
decls={};theorems={}
for m,src in SOURCES.items():
    s=src.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',s)
    decls[m]=[NS[m]+'.'+n for n in re.findall(pattern,s,re.M)]
    theorems[m]=re.findall(r'^(?:theorem|lemma)\s+([^\s(:]+)',s,re.M)
    (G/'replay-sources'/src.name).write_bytes(src.read_bytes())
client=G/'replay-sources/IndependentClient.lean'
decls['IndependentClient']=['IndependentAdjointReview.'+n for n in re.findall(pattern,client.read_text(),re.M)]
audit='\n'.join('import '+m for m in MODULES+['IndependentClient'])+'\n'
names=[n for group in decls.values() for n in group]
assert len(names)==len(set(names))
audit+='\n'.join('#print axioms '+n for n in names)+'\n'
(G/'replay-sources/Audit.lean').write_text(audit)

original=(B/'ComplexAdjoint.lean').read_text()
mutations={
 'ScalarFixedMutation':('bar (z • a) = star z • bar a','bar (z • a) = z • bar a'),
 'OrderPreservingMutation':('bar (a*b) = bar b * bar a := star_mul a b','bar (a*b) = bar a * bar b := star_mul a b'),
 'MissingIMutation':('def iAnti (a b : CCl) : CCl := Complex.I • (a*b+b*a)','def iAnti (a b : CCl) : CCl := a*b+b*a')}
for name,(old,new) in mutations.items():
    assert original.count(old)==1
    (G/'replay-sources'/(name+'.lean')).write_text(original.replace(old,new))
(G/'replay-sources/WrongAdjointClient.lean').write_text('''import AdjointControls
open GUComplex
example : fixedBar (iAnti (cgamma 0) (cgamma 0)) = -iAnti (cgamma 0) (cgamma 0) := by
  exact iAnti_skew (cgamma 0) (cgamma 0) (gamma_skew 0) (gamma_skew 0)
''')

with tempfile.TemporaryDirectory(prefix='adjoint-review-',dir=G/'cache') as tmp:
    work=Path(tmp);env['LEAN_PATH']=str(work)+':'+':'.join(deps)
    for p in (G/'replay-sources').glob('*.lean'):
        (work/p.name).write_bytes(p.read_bytes())
    for m in MODULES+['IndependentClient']:
        if m in SOURCES: assert digest(work/(m+'.lean'))==digest(SOURCES[m])
        run('fresh-'+m,[lean,'--root='+str(work),'-o',str(work/(m+'.olean')),str(work/(m+'.lean'))],work)
    out=run('all-declaration-axioms',[lean,str(work/'Audit.lean')],work)
    ax={n:[v.strip() for v in vals.split(',') if v.strip()] for n,vals in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
    ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",out)})
    assert set(ax)==set(names),(set(names)-set(ax),set(ax)-set(names))
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values())
    for m in MODULES+['IndependentClient']:
        run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'],work)
    for name in list(mutations)+['WrongAdjointClient']:
        out=run('negative-'+name,[lean,str(work/(name+'.lean'))],work,success=False)
        assert any(s in out for s in ['unsolved goals','Type mismatch','Tactic `rewrite` failed'])
        assert not any(s in out.lower() for s in ['unknown module','unknown identifier','file not found'])

after=state();assert before==after
(G/'hashes-after.json').write_text(json.dumps(after,indent=2)+'\n')
result={'accepted':True,'builder_manifest_sha256':EXPECTED,'new_builder_files_unchanged':35,
 'dependency_builder_files_unchanged':34,'fresh_target_modules':NEW,'fresh_local_dependencies':DEPS,
 'new_public_theorems':sum(len(theorems[m]) for m in NEW),'inherited_public_theorems':sum(len(theorems[m]) for m in DEPS),
 'new_named_declarations':sum(len(decls[m]) for m in NEW),'inherited_named_declarations':sum(len(decls[m]) for m in DEPS),
 'independent_client_declarations':len(decls['IndependentClient']),'declarations':decls,'axioms':ax,
 'lean':version,'mathlib_revision':revision,'steps':steps,
 'scope':'Fresh copied local sources and target oleans; pinned prebuilt Mathlib reused. Each of seven modules and the independent client separately replayed.'}
(G/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['accepted','new_public_theorems','new_named_declarations','inherited_public_theorems','inherited_named_declarations','independent_client_declarations']}),flush=True)
