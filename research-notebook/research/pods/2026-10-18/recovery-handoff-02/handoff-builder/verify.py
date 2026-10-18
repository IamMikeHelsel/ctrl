#!/usr/bin/env python3
"""Fresh copied-source builds, all stated theorem audits, separate kernel replay.
Writes only within this handoff-builder folder; no Git or network commands.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BASE=WORK/'lean-controls'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=str(WORK/'.tools/elan/bin/lake')
    def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
    lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
    paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
    paths=[p for p in paths if '.lake/packages/' in p]
    root=HERE/'fresh-replay';root.mkdir(exist_ok=True)
    for p in root.rglob('*'):
        if p.is_file():p.unlink()
    env['LEAN_PATH']=str(root)+':'+':'.join(paths)
    env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    sources={'DigitalHold':HERE/'inputs/DigitalHold.lean'}
    sources.update({m:HERE/(m+'.lean') for m in ['DelayedHold','DelayedWitness','BrakingDelayedHold','BrakingDelayedWitness']})
    original={m:sha(p) for m,p in sources.items()}
    assert original['DigitalHold']=='aa91b649affc0906c79dd7a017b34d6f729d1c16f50117ab87daaa1ed2fadc03'
    assert all(not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text()) for p in sources.values())
    logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
    report={'passed':False,'scope':'Every listed local source copied and compiled fresh. Only pinned external package build products reused; no local project proof cache in LEAN_PATH.',
      'source_sha256':original,'verifier_sha256':sha(Path(__file__)),
      'toolchain':query('lean','--version'),'lean_sha256':sha(Path(lean)),'leanchecker_sha256':sha(Path(checker)),
      'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),
      'package_revisions':json.loads((BASE/'lake-manifest.json').read_text())['packages'],
      'lean_path':env['LEAN_PATH'],'steps':[],'axioms':{}}
    def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(label,args,negative=False):
        start=time.monotonic()
        with (logs/(label+'.log')).open('w') as out:
            p=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
        ok=p.returncode!=0 if negative else p.returncode==0
        raw=(logs/(label+'.log')).read_text()
        if negative:ok=ok and 'error:' in raw and ('unsolved goals' in raw or 'linarith failed' in raw) and 'unknownIdentifier' not in raw and 'unknown module' not in raw
        report['steps'].append({'label':label,'exit_code':p.returncode,'passed':ok,'expected':'rejection' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(logs/(label+'.log'))})
        save();print(label,p.returncode,ok,flush=True)
        if not ok:raise RuntimeError(label)
    names=[]
    for m,p in sources.items():
        shutil.copy2(p,root/(m+'.lean'))
        run('fresh-build-'+m,[lean,'--root='+str(root),'-o',str(root/(m+'.olean')),str(root/(m+'.lean'))])
        text=p.read_text();ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
        names.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M))
    audit='import DelayedWitness\nimport BrakingDelayedWitness\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
    (HERE/'Audit.lean').write_text(audit);(root/'Audit.lean').write_text(audit)
    run('axiom-audit',[lean,str(root/'Audit.lean')])
    for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
        axioms={x.strip() for x in raw.split(',') if x.strip()};assert axioms<=ALLOWED,(name,axioms)
        report['axioms'][name]=sorted(axioms)
    assert set(report['axioms'])==set(names),set(names)-set(report['axioms'])
    for m in sources:run('kernel-'+m,[checker,m,'-v'])
    negatives=HERE/'negative-controls';negatives.mkdir(exist_ok=True)
    originaltext=sources['BrakingDelayedHold'].read_text()
    for label,old,new in [
        ('reject-5ms-information-age','t-stamp b t ≤ 1/1000','t-stamp b t ≤ 1/200'),
        ('reject-5ms-startup-limit','def startupLimit : ℝ := 1/2000','def startupLimit : ℝ := 1/200')]:
        assert originaltext.count(old)==1
        p=negatives/(label+'.lean');p.write_text(originaltext.replace(old,new))
        run(label,[lean,'--root='+str(negatives),str(p)],negative=True)
    falseclaims={
      'reject-pending-minus-two-slope-eight': '|-8*(-1/100:ℝ)-6*(-117/100)-12*(-2-(-117/100))/2| ≤ 8',
      'reject-braking-pending-slope-seven': '|-8*(-1/50:ℝ)-6*(-61/50)-8*((-121/100)+(-1/100)-(-61/50))/2| ≤ 7',
      'reject-extra-first-hold-age': '(3/2000:ℝ)-0 ≤ 1/1000'}
    for label,claim in falseclaims.items():
        p=negatives/(label+'.lean');p.write_text('import BrakingDelayedHold\nexample : '+claim+' := by norm_num\n')
        run(label,[lean,'--root='+str(negatives),str(p)],negative=True)
    report['source_unchanged']=all(sha(p)==original[m] for m,p in sources.items())
    report['theorem_count']=len(names)
    report['passed']=report['source_unchanged'] and all(s['passed'] for s in report['steps'])
    save();print(json.dumps({'passed':report['passed'],'theorems':len(names)}))
if __name__=='__main__':main()
