"""Independent fresh build and semantic review. Writes only critic-01."""
from pathlib import Path
import os, subprocess, hashlib, json, re, time

B=Path(__file__).resolve().parent
A=B.parent/'analyst-01'
R=B.parents[4]
L=R/'lean-controls'
T=B/'cache'
mods=['CliffordModel','HyperbolicSpinor','SpinorDimensions','SplitSpinor']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'SHA256SUMS')=='0c667224d83d64fc6cd9b764e1a556da23e5c7f90ef462b5f5f35149e60f579e'
frozen=[]
for line in (A/'SHA256SUMS').read_text().splitlines():
    h,p=line.split('  ',1)
    assert sha(A/p)==h,p
    frozen.append(p)
env=os.environ.copy()
env['ELAN_HOME']=str(R/'.tools/elan')
lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=L,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=L,env=env,text=True).strip().split(':')
env['LEAN_PATH']=str(T)+':'+':'.join(str((L/p).resolve()) for p in paths)
env['PATH']=str(Path(lean).parent)+':'+env['PATH']
steps=[]
def run(name,cmd,negative=False):
    start=time.monotonic()
    p=subprocess.run(cmd,cwd=T,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=240)
    (B/'logs'/(name+'.txt')).write_text(p.stdout)
    steps.append(dict(name=name,returncode=p.returncode,seconds=round(time.monotonic()-start,3),command=cmd))
    print(name,p.returncode,flush=True)
    assert (p.returncode!=0 if negative else p.returncode==0),p.stdout
    if negative:
        assert not any(e in p.stdout.lower() for e in ['unknown identifier','unknown module','file not found'])
    return p.stdout
names=[]
for m in mods:
    s=(A/(m+'.lean')).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
    (T/(m+'.lean')).write_text(s)
    names.extend(('GUClifford.' if m=='CliffordModel' else 'HyperbolicSpinor.')+n for n in re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma|def|abbrev)\s+([^\s(:]+)',s,re.M))
    run('build-'+m,[lean,'--root='+str(T),'-o',str(T/(m+'.olean')),str(T/(m+'.lean'))])
audit='import SplitSpinor\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
(B/'Audit.lean.txt').write_text(audit)
(T/'Audit.lean').write_text(audit)
out=run('axioms',[lean,str(T/'Audit.lean')])
axioms={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",out)})
assert set(axioms)==set(names)
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
for m in mods:
    run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'])
for fname in ['ReviewClient','WrongNegativeSquare','WrongMixedFactor','WrongDimension']:
    src=B/(fname+'.lean.txt')
    (T/(fname+'.lean')).write_bytes(src.read_bytes())
    run(fname,[lean,'--root='+str(T),'-o',str(T/(fname+'.olean')),str(T/(fname+'.lean'))],fname!='ReviewClient')
run('kernel-ReviewClient',[str(Path(lean).with_name('leanchecker')),'ReviewClient','-v'])
for line in (A/'SHA256SUMS').read_text().splitlines():
    h,p=line.split('  ',1);assert sha(A/p)==h,p
result={'status':'PASS','frozen_manifest':sha(A/'SHA256SUMS'),'frozen_files_verified':len(frozen),'source_hashes':{m:sha(A/(m+'.lean')) for m in mods},'public_declaration_count':len(names),'axioms':axioms,'steps':steps,'lean_version':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),'mathlib_revision':json.loads((L/'lake-manifest.json').read_text())['packages'][0]['rev'],'scope':'Four fresh local modules, all public definitions/theorems, separate local kernel replay, independent semantic client, three false clients. Pinned prebuilt mathlib reused.'}
(B/'lean-review.json').write_text(json.dumps(result,indent=2)+'\n')
