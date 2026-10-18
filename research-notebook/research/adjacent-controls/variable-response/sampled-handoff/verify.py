#!/usr/bin/env python3
"""Fresh source replay for noisy capture and robust position holding."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[3]
BASE=WORK/'lean-controls'
DEPS=['ComparisonEnvelope','FirstStop','StoppingCertificate','ActualStop']
MODULES=['Capture','RobustHold','ReleaseCounterexample','Handoff']
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=str(WORK/'.tools/elan/bin/lake')
    def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
    lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
    dep=':'.join(str((BASE/p).resolve())if not Path(p).is_absolute()else p for p in query('printenv','LEAN_PATH').split(':'))
    sources={m:(HERE.parent if m in DEPS else HERE)/(m+'.lean')for m in DEPS+MODULES}
    original=json.loads((HERE.parent/'verification.json').read_text())
    assert original['passed']
    for m in DEPS:assert sha(sources[m])==original['source_sha256'][m+'.lean'],m
    logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
    report={'passed':False,'scope':'Fresh four target modules and four local dependency sources. Kernel replay for each target. Pinned LeanControls/mathlib artifacts reused.',
      'toolchain':query('lean','--version'),'source_sha256':{m:sha(p)for m,p in sources.items()},
      'verifier_sha256':sha(Path(__file__)),'steps':[],'axioms':{},
      'mathlib_commit':subprocess.check_output(['git','-C',str(BASE/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()}
    def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(label,args,cwd,renv,negative=False):
        start=time.monotonic()
        with (logs/(label+'.log')).open('w')as out:
            p=subprocess.run(args,cwd=cwd,env=renv,stdout=out,stderr=subprocess.STDOUT)
        ok=p.returncode!=0 if negative else p.returncode==0
        report['steps'].append({'label':label,'exit_code':p.returncode,'passed':ok,
          'expected':'rejection'if negative else'success','seconds':time.monotonic()-start,'log_sha256':sha(logs/(label+'.log'))})
        save();print(label,p.returncode,flush=True)
        assert ok,label
    with tempfile.TemporaryDirectory(prefix='sampled-hold-lean-')as tmp:
        root=Path(tmp);renv=env.copy();renv['LEAN_PATH']=str(root)+':'+dep
        renv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
        names=[]
        for m,p in sources.items():
            shutil.copy2(p,root/p.name)
            if m in MODULES:
                text=p.read_text();ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
                names.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M))
            run('build-'+m,[lean,'--root='+str(root),'-o',str(root/(m+'.olean')),str(root/p.name)],root,renv)
        (root/'Audit.lean').write_text('\n'.join(['import '+m for m in MODULES]+['#print axioms '+n for n in names])+'\n')
        run('axiom-audit',[lean,str(root/'Audit.lean')],root,renv)
        for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
            axioms={x.strip()for x in raw.split(',')if x.strip()};assert axioms<=ALLOWED,(name,axioms)
            report['axioms'][name]=sorted(axioms)
        assert set(report['axioms'])==set(names)
        for m in MODULES:run('kernel-'+m,[checker,m,'-v'],root,renv)
        source=(root/'Capture.lean').read_text();old='exampleCenter+exampleRadius ≤ 3/20 := by'
        assert source.count(old)==1
        (root/'FalseTube.lean').write_text(source.replace(old,'exampleCenter+exampleRadius ≤ 7/50 := by'))
        run('reject-false-tube',[lean,str(root/'FalseTube.lean')],root,renv,negative=True)
        log=(logs/'reject-false-tube.log').read_text()
        assert 'unsolved goals' in log and 'unknown' not in log
    report['source_unchanged']=all(sha(p)==report['source_sha256'][m]for m,p in sources.items())
    report['theorem_count']=len(names)
    report['passed']=report['source_unchanged']and all(s['passed']for s in report['steps'])
    save();print(json.dumps({'passed':report['passed'],'theorem_count':len(names)}))
if __name__=='__main__':main()
