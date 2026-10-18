#!/usr/bin/env python3
"""Fresh build, axiom audit and kernel replay of the release counterexample.

This does NOT check the Python interval trace or prove direct-feedback safety.
Pinned LeanControls and mathlib build artifacts are retained as dependencies.
"""
import hashlib, json, os, re, shutil, subprocess, tempfile, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = ROOT/'lean-controls'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    env = os.environ.copy()
    lake = str(ROOT/'.tools/elan/bin/lake')
    env['ELAN_HOME'] = str(ROOT/'.tools/elan')
    def read(*args):
        return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
    lean = read('which','lean')
    dep = ':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute() else p
                   for p in read('printenv','LEAN_PATH').split(':'))
    source = HERE/'DirectSwitch.lean'
    names = re.findall(r'^theorem (\w+)',source.read_text(),re.M)
    report = {'passed':False,'scope':__doc__,'source_sha256':sha(source),
              'verifier_sha256':sha(Path(__file__)),'toolchain':read('lean','--version'),
              'steps':[],'axioms':{}}
    logs = HERE/'switch-verification-logs'; logs.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='direct-switch-') as td:
        temp = Path(td); shutil.copy2(source,temp/source.name)
        env['LEAN_PATH'] = str(temp)+':'+dep
        env['PATH'] = str(Path(lean).parent)+os.pathsep+env.get('PATH','')
        def run(label,cmd):
            started=time.monotonic()
            p=subprocess.run(cmd,cwd=temp,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            (logs/(label+'.txt')).write_text(p.stdout)
            report['steps'].append({'label':label,'command':cmd,'exit_code':p.returncode,
                'seconds':time.monotonic()-started,'log_sha256':sha(logs/(label+'.txt'))})
            (HERE/'switch-verification.json').write_text(json.dumps(report,indent=2)+'\n')
            print(label,p.returncode,flush=True)
            if p.returncode: raise RuntimeError(p.stdout)
            return p.stdout
        run('fresh-build',[lean,'--root='+td,'-o',str(temp/'DirectSwitch.olean'),str(temp/source.name)])
        (temp/'Audit.lean').write_text('import DirectSwitch\n'+'\n'.join(
            '#print axioms LeanControls.DirectSwitch.'+n for n in names)+'\n')
        audit=run('axiom-audit',[lean,str(temp/'Audit.lean')])
        for name,ax in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",audit):
            axioms={x.strip() for x in ax.split(',') if x.strip()}
            assert axioms <= {'propext','Classical.choice','Quot.sound'}
            report['axioms'][name]=sorted(axioms)
        assert len(report['axioms'])==len(names)==10
        run('kernel-replay',[str(Path(lean).with_name('leanchecker')),'DirectSwitch','-v'])
    assert sha(source)==report['source_sha256']
    report['passed']=True
    report['theorem_count']=len(names)
    (HERE/'switch-verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Passed: 10 declarations; direct-feedback safety remains open.')

if __name__=='__main__': main()
