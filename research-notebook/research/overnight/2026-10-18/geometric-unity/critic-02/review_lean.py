"""Independent review of the real matrix-equivalence gate. No frozen writes."""
from pathlib import Path
import os, subprocess, hashlib, json, re, time
B=Path(__file__).resolve().parent;A=B.parent/'builder-02';R=B.parents[4];L=R/'lean-controls';T=B/'cache'
mods=['CliffordModel','HyperbolicSpinor','SpinorDimensions','SplitSpinor','FockOperators','VacuumProjector','FockImage','WordActions','MatrixUnits','FullImage','RealEquivalence','OrderControls','BasisActions']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={
 'builder-02':'fab7240941cb89b4517fd2614160f7ebf122eff095b017f4676bd09cd94b792d',
 'analyst-01':'0c667224d83d64fc6cd9b764e1a556da23e5c7f90ef462b5f5f35149e60f579e',
 'critic-01':'d525512033db6160c60ee77cc032a68e103253fa6604c620deb79077d4e640d3',
}
oldpins={
 R/'research/pods/2026-10-17/weinstein/clifford-contraction-03/builder':'a283b2848de505c7565eb768e35215d9330f2eedfc015d51876fb29784aaf085',
 R/'research/pods/2026-10-17/weinstein/complex-adjoint-04/builder':'c498ef42bd3d8c428a0dcab1c34d4ca1eb41e419d57a47f00fdb6eca18cb7e0e',
}
def check_frozen():
    result={}
    for folder,digest in {**{B.parent/f:d for f,d in pins.items()},**oldpins}.items():
        m=folder/'SHA256SUMS';assert sha(m)==digest,(folder,'manifest')
        entries=m.read_text().splitlines()
        for line in entries:
            h,p=line.split('  ',1);assert sha(folder/p)==h,(folder,p)
        result[str(folder.relative_to(R))]={'sha256':digest,'files':len(entries)}
    for m in mods[:4]:assert sha(A/(m+'.lean'))==sha(B.parent/'analyst-01'/(m+'.lean'))
    return result
frozen=check_frozen()
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=L,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=L,env=env,text=True).strip().split(':')
env['LEAN_PATH']=str(T)+':'+':'.join(str((L/p).resolve()) for p in paths)
env['PATH']=str(Path(lean).parent)+':'+env['PATH']
steps=[]
def run(name,cmd,negative=False):
    start=time.monotonic();p=subprocess.run(cmd,cwd=T,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    (B/'logs'/(name+'.txt')).write_text(p.stdout)
    steps.append(dict(name=name,returncode=p.returncode,seconds=round(time.monotonic()-start,3),command=cmd))
    (B/'run-progress.json').write_text(json.dumps(steps,indent=2)+'\n')
    print(name,p.returncode,flush=True)
    assert (p.returncode!=0 if negative else p.returncode==0),p.stdout
    if negative:assert not any(e in p.stdout.lower() for e in ['unknown identifier','unknown module','file not found','failed to synthesize'])
    return p.stdout
names=[]
for m in mods:
    s=(A/(m+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
    (T/(m+'.lean')).write_text(s)
    names.extend(('GUClifford.' if m=='CliffordModel' else 'HyperbolicSpinor.')+n for n in re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma|def|abbrev)\s+([^\s(:]+)',s,re.M))
    run('build-'+m,[lean,'--root='+str(T),'-o',str(T/(m+'.olean')),str(T/(m+'.lean'))])
audit='import OrderControls\nimport BasisActions\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
(B/'Audit.lean.txt').write_text(audit);(T/'Audit.lean').write_text(audit)
out=run('axioms',[lean,str(T/'Audit.lean')])
axioms={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",out)})
assert set(axioms)==set(names)
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
for name in ['ReviewClient','WrongInsertionSign','WrongAnnihilationOrder','WrongVacuumOrder','WrongPreimageFactor']:
    (T/(name+'.lean')).write_bytes((B/(name+'.lean.txt')).read_bytes())
    run(name,[lean,'--root='+str(T),'-o',str(T/(name+'.olean')),str(T/(name+'.lean'))],name!='ReviewClient')
client_names=re.findall(r'^theorem\s+([^\s(:]+)',(B/'ReviewClient.lean.txt').read_text(),re.M)
client_audit='import ReviewClient\n'+'\n'.join('#print axioms '+n for n in client_names)+'\n'
(B/'ClientAxioms.lean.txt').write_text(client_audit);(T/'ClientAxioms.lean').write_text(client_audit)
cout=run('client-axioms',[lean,str(T/'ClientAxioms.lean')])
client_axioms={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",cout)}
assert set(client_axioms)==set(client_names)
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in client_axioms.values())
for m in mods:run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'])
run('kernel-ReviewClient',[str(Path(lean).with_name('leanchecker')),'ReviewClient','-v'])
assert check_frozen()==frozen
result={'status':'PASS','source_hashes':{m:sha(A/(m+'.lean')) for m in mods},'public_declarations':names,'public_count':len(names),'axioms':axioms,'reviewer_named_theorem_axioms':client_axioms,'steps':steps,'frozen_evidence':frozen,'client_harness_failure_preserved':{'file':'builder-02/attempts/Client-noncomputable-01.log','sha256':sha(A/'attempts/Client-noncomputable-01.log')},'lean':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),'mathlib':json.loads((L/'lake-manifest.json').read_text())['packages'][0]['rev'],'boundary':'Fresh local closure and separate kernel replay. Pinned prebuilt mathlib reused. No complex adjoint, signature or GU operator result follows from this gate.'}
(B/'lean-review.json').write_text(json.dumps(result,indent=2)+'\n')
