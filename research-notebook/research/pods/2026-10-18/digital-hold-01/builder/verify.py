#!/usr/bin/env python3
"""Fresh local source, audit, independent Lean kernel replay, negative controls.
All writes stay under builder/. Pinned Mathlib artifacts are reused.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time,sys
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BASE=WORK/'lean-controls'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=str(WORK/'.tools/elan/bin/lake')
    def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
    lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
    # Exclude local project build products. The new module has only Mathlib imports.
    paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
    paths=[p for p in paths if '.lake/packages/' in p]
    root=HERE/'fresh-replay';root.mkdir(exist_ok=True)
    for p in root.rglob('*'):
        if p.is_file():p.unlink()
    env['LEAN_PATH']=str(root)+':'+':'.join(paths)
    env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    source=HERE/'DigitalHold.lean';original=sha(source);text=source.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',text)
    assert all(x.startswith('Mathlib.') for x in re.findall(r'^public import (\S+)',text,re.M))
    logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
    report={'passed':False,'scope':'Self-contained local DigitalHold source compiled fresh; all imported Mathlib artifacts use the frozen local pin. No cached local proof module appears in LEAN_PATH.',
      'source_sha256':original,'verifier_sha256':sha(Path(__file__)),
      'toolchain':query('lean','--version'),'lean_sha256':sha(Path(lean)),'leanchecker_sha256':sha(Path(checker)),
      'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),
      'mathlib_commit':subprocess.check_output(['git','-C',str(BASE/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),
      'mathlib_tracked_patch_sha256':hashlib.sha256(subprocess.check_output(['git','-C',str(BASE/'.lake/packages/mathlib'),'diff','--binary','HEAD'])).hexdigest(),
      'lean_path':env['LEAN_PATH'],'steps':[],'axioms':{}}
    def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(label,args,negative=False):
        start=time.monotonic()
        with (logs/(label+'.log')).open('w') as out:
            p=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
        ok=p.returncode!=0 if negative else p.returncode==0
        raw=(logs/(label+'.log')).read_text()
        if negative:
            ok=ok and 'error:' in raw and ('unsolved goals' in raw or 'linarith failed' in raw) and 'unknownIdentifier' not in raw and 'unknown module' not in raw
        report['steps'].append({'label':label,'exit_code':p.returncode,'passed':ok,'expected':'rejection' if negative else 'success',
          'seconds':round(time.monotonic()-start,4),'log_sha256':sha(logs/(label+'.log'))})
        save();print(label,p.returncode,ok,flush=True)
        if not ok:raise RuntimeError(label)
    shutil.copy2(source,root/'DigitalHold.lean')
    run('fresh-build',[lean,'--root='+str(root),'-o',str(root/'DigitalHold.olean'),str(root/'DigitalHold.lean')])
    names=['LeanControls.DigitalHold.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
    (root/'Audit.lean').write_text('import DigitalHold\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
    run('axiom-audit',[lean,str(root/'Audit.lean')])
    for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
        axioms={x.strip() for x in raw.split(',') if x.strip()};assert axioms<=ALLOWED,(name,axioms)
        report['axioms'][name]=sorted(axioms)
    assert set(report['axioms'])==set(names),set(names)-set(report['axioms'])
    run('kernel-DigitalHold',[checker,'DigitalHold','-v'])
    negatives=HERE/'negative-controls';negatives.mkdir(exist_ok=True)
    for label,old,new in [
        ('reject-5ms-age','t-stamp b t ≤ 1/1000','t-stamp b t ≤ 1/200'),
        ('reject-smaller-cube','def radius : ℝ := 2221/40000','def radius : ℝ := 1/20')]:
        assert text.count(old)==1
        p=negatives/(label+'.lean');p.write_text(text.replace(old,new))
        run(label,[lean,'--root='+str(negatives),str(p)],negative=True)
    report['source_unchanged']=sha(source)==original
    report['theorem_count']=len(names)
    report['passed']=report['source_unchanged'] and all(x['passed'] for x in report['steps'])
    save();print(json.dumps({'passed':report['passed'],'theorems':len(names)}))
if __name__=='__main__':main()
