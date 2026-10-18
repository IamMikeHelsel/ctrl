"""Fresh copied-source build, all public theorem axioms, kernel replay, false sign."""
from pathlib import Path
import hashlib, json, os, re, subprocess, tempfile, time

B=Path(__file__).resolve().parent
R=B.parents[5]
BASE=R/'lean-controls'
MODULES=['CliffordModel','ContractionAlgebra','CliffordContraction','CliffordControls']
PREFIX={'CliffordModel':'GUClifford','ContractionAlgebra':'GUContraction',
        'CliffordContraction':'GUClifford','CliffordControls':'GUClifford'}
ANALYST=B.parent.parent/'definition-audit-02/analyst'
ANALYST_MANIFEST='fd33e27a0bc042954cb27d94876cdc83d2c45747c557da24f90ce51343d31ed7'
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan')
lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=BASE,env=env,text=True).strip().split(':')
depaths=[str((BASE/p).resolve()) for p in paths]
env['PATH']=str(Path(lean).parent)+':'+env['PATH']
logs=B/'logs';logs.mkdir(exist_ok=True)
(B/'cache').mkdir(exist_ok=True)
records=[]

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def check_analyst():
    assert sha(ANALYST/'SHA256SUMS')==ANALYST_MANIFEST
    for line in (ANALYST/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1)
        assert sha(ANALYST/name)==digest,name

def run(name,args,cwd,expect_failure=False):
    start=time.monotonic()
    with (logs/(name+'.log')).open('w') as out:
        p=subprocess.run(args,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=300)
    rec={'step':name,'command':args,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3)}
    records.append(rec)
    print({k:v for k,v in rec.items() if k!='command'},flush=True)
    output=(logs/(name+'.log')).read_text()
    assert (p.returncode!=0 if expect_failure else p.returncode==0),output[-12000:]
    return output

check_analyst()
sources={m:B/(m+'.lean') for m in MODULES}
hashes={m:sha(p) for m,p in sources.items()}
for m,p in sources.items():
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',p.read_text()),m

with tempfile.TemporaryDirectory(prefix='clifford-fresh-',dir=B/'cache') as temp:
    tmp=Path(temp)
    env['LEAN_PATH']=str(tmp)+':'+':'.join(depaths)
    for m,p in sources.items():
        (tmp/(m+'.lean')).write_bytes(p.read_bytes())
        assert sha(tmp/(m+'.lean'))==hashes[m]
        run('fresh-'+m,[lean,'--root='+str(tmp),'-o',str(tmp/(m+'.olean')),str(tmp/(m+'.lean'))],tmp)
    names=[]
    for m,p in sources.items():
        names += [PREFIX[m]+'.'+name for name in re.findall(r'^theorem\s+([^\s(]+)',p.read_text(),re.M)]
    assert len(names)==len(set(names))
    audit='\n'.join('import '+m for m in MODULES)+'\n'+'\n'.join('#print axioms '+name for name in names)+'\n'
    (tmp/'Audit.lean').write_text(audit)
    (B/'Audit.lean.txt').write_text(audit)
    output=run('axioms',[lean,str(tmp/'Audit.lean')],tmp)
    axioms={n:[a.strip() for a in deps.split(',') if a.strip()] for n,deps in
            re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",output)}
    axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",output)})
    assert set(axioms)==set(names),(set(names)-set(axioms),set(axioms)-set(names))
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values()),axioms
    for m in MODULES:
        run('kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'],tmp)

    client='''import CliffordControls
open GUClifford GUContraction
example (R:Tensor) (h:Curvature R) : K R=algebraMap ℝ Cl (-scal R) :=
  actual_clifford_contraction R h
example (R:Tensor) (h:PairSymmetries R) : total (rho R) gamma=(2:ℝ) • K R :=
  actual_normalization_bridge R h
example : K sectional=algebraMap ℝ Cl (-2) := sectional_K
example : K fourform=(12:ℝ) • blade0123 := fourform_K
example : K fourform≠0 := fourform_K_ne_zero
example : ¬(∀ R:Tensor, PairSymmetries R → K R=algebraMap ℝ Cl (-scal R)) :=
  no_universal_without_bianchi
'''
    (tmp/'Client.lean').write_text(client);(B/'Client.lean.txt').write_text(client)
    run('client',[lean,str(tmp/'Client.lean')],tmp)

    original=sources['CliffordContraction'].read_text()
    needle='K R = algebraMap ℝ Cl (-scal R)'
    assert original.count(needle)==1
    mutation=original.replace(needle,'K R = algebraMap ℝ Cl (scal R)')
    (tmp/'FalseSignMutation.lean').write_text(mutation)
    (B/'FalseSignMutation.lean.txt').write_text(mutation)
    fail=run('false-sign-mutation',[lean,str(tmp/'FalseSignMutation.lean')],tmp,True)
    assert ('unsolved goals' in fail or 'Type mismatch' in fail),fail
    assert 'unknown module' not in fail.lower() and 'unknown identifier' not in fail.lower(),fail

    falseclient='''import CliffordControls
open GUClifford
example : K sectional=algebraMap ℝ Cl (scal sectional) := by
  exact actual_clifford_contraction sectional sectional_curvature
'''
    (tmp/'FalseSignClient.lean').write_text(falseclient)
    (B/'FalseSignClient.lean.txt').write_text(falseclient)
    fail=run('false-sign-client',[lean,str(tmp/'FalseSignClient.lean')],tmp,True)
    assert 'Type mismatch' in fail and 'actual_clifford_contraction' in fail,fail
    assert 'unknown module' not in fail.lower() and 'unknown identifier' not in fail.lower(),fail

    assert all(sha(p)==hashes[m] for m,p in sources.items())
    check_analyst()
    manifest=json.loads((BASE/'lake-manifest.json').read_text())
    revision=next(x['rev'] for x in manifest['packages'] if x['name']=='mathlib')
    assert revision=='56a005855ea17e0b0958f73ec801ae140b0a1679'
    report={'passed':True,'source_sha256':hashes,'theorem_count':len(names),'axioms':axioms,
            'steps':records,'target_modules':MODULES,
            'lean':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),
            'toolchain':(BASE/'lean-toolchain').read_text().strip(),
            'mathlib_manifest_revision':revision,'frozen_analyst_manifest_preserved':True,
            'scope':'Fresh copies and fresh target oleans; pinned prebuilt Mathlib dependencies reused. Every public theorem audited. All four modules separately replayed by leanchecker. The sign-mutated theorem and false sectional client were rejected. Dropped Bianchi is refuted by the explicit nonzero four-form and a universal-impossibility theorem.'}
    (B/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['passed','theorem_count','source_sha256','lean','mathlib_manifest_revision']},indent=2),flush=True)
