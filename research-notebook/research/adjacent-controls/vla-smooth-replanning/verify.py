#!/usr/bin/env python3
"""Fresh source build, transitive axiom audit, and standalone kernel replay."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

HERE=Path(__file__).resolve().parent
WORK=HERE.parents[2]
BASE=WORK/'lean-controls'
MODULES=['SmoothReplan']
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=str(WORK/'.tools/elan/bin/lake')
    def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
    lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
    dep=':'.join(str((BASE/p).resolve())if not Path(p).is_absolute()else p for p in query('printenv','LEAN_PATH').split(':'))
    hashes={m+'.lean':digest(HERE/(m+'.lean'))for m in MODULES}
    logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
    report={'scope':'Fresh new sources and individual kernel replay; pinned LeanControls and mathlib artifacts reused.',
      'toolchain':query('lean','--version'),'source_sha256':hashes,'verifier_sha256':digest(Path(__file__)),
      'mathlib_commit':subprocess.check_output(['git','-C',str(BASE/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),
      'steps':[],'axioms':{},'passed':False}
    def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(label,cmd,cwd,runenv,negative=False):
        started=time.monotonic()
        with (logs/(label+'.log')).open('w')as out:
            proc=subprocess.run(cmd,cwd=cwd,env=runenv,stdout=out,stderr=subprocess.STDOUT)
        good=(proc.returncode!=0 if negative else proc.returncode==0)
        report['steps'].append({'label':label,'exit_code':proc.returncode,'expected':'rejection'if negative else'success',
          'passed':good,'seconds':time.monotonic()-started,'log_sha256':digest(logs/(label+'.log'))})
        save();print(label,proc.returncode,f'{time.monotonic()-started:.2f}s',flush=True)
        if not good:raise RuntimeError('Unexpected result: '+label)
    with tempfile.TemporaryDirectory(prefix='smooth-replan-lean-')as tmp:
        root=Path(tmp);checkenv=env.copy();checkenv['LEAN_PATH']=str(root)+':'+dep
        checkenv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
        audit=['import '+m for m in MODULES]
        names=[]
        for m in MODULES:
            src=HERE/(m+'.lean');shutil.copy2(src,root/src.name)
            text=src.read_text();ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
            names += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
            run('build-'+m,[lean,f'--root={root}','-o',str(root/(m+'.olean')),str(root/src.name)],root,checkenv)
        audit += ['#print axioms '+n for n in names]
        (root/'Audit.lean').write_text('\n'.join(audit)+'\n')
        run('axiom-audit',[lean,str(root/'Audit.lean')],root,checkenv)
        log=(logs/'axiom-audit.log').read_text()
        for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log):
            ax={a.strip()for a in raw.split(',')if a.strip()};assert ax<=ALLOWED,(name,ax)
            report['axioms'][name]=sorted(ax)
        assert set(report['axioms'])==set(names),'Incomplete axiom audit'
        for m in MODULES:run('kernel-'+m,[checker,m,'-v'],root,checkenv)
        source=(root/'SmoothReplan.lean').read_text()
        old='Admission ⟨0,1/10,0⟩ 10 (1/50) (-1/100) (1/100) (1/5) 1 10 := by'
        assert source.count(old)==1
        bad=source.replace(old,old.replace('1 10 := by','1 1 := by'))
        (root/'FalseAdmission.lean').write_text(bad)
        run('reject-false-admission',[lean,str(root/'FalseAdmission.lean')],root,checkenv,negative=True)
        rejection=(logs/'reject-false-admission.log').read_text()
        assert 'unsolved goals' in rejection and 'error: unknown' not in rejection
    report['false_admission_rejected']=True
    report['source_unchanged']=all(digest(HERE/name)==value for name,value in hashes.items())
    report['theorem_count']=len(names)
    report['passed']=report['source_unchanged']and all(s['passed']for s in report['steps'])
    save();print(json.dumps({'passed':report['passed'],'theorem_count':len(names)}))

if __name__=='__main__':main()
