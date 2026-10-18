#!/usr/bin/env python3
"""Fresh-source builds, exhaustive target-statement audit, kernel replay, false mutation."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BASE=WORK/'lean-controls'
DEPS=['ComparisonEnvelope']
MODULES=['QuadraticSlowFilter']
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    subprocess.run([os.sys.executable,str(HERE/'check_exact.py')],check=True)
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=str(WORK/'.tools/elan/bin/lake')
    def query(*a):return subprocess.check_output([lake,'env',*a],cwd=BASE,env=env,text=True).strip()
    lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
    dep=':'.join(str((BASE/p).resolve())if not Path(p).is_absolute()else p for p in query('printenv','LEAN_PATH').split(':'))
    sources={'ComparisonEnvelope':WORK/'research/adjacent-controls/variable-response/ComparisonEnvelope.lean'}
    sources.update({m:HERE/(m+'.lean') for m in MODULES})
    logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
    report={'passed':False,'scope':'One target module and ComparisonEnvelope source built fresh; separate kernel replay for target. Pinned LeanControls/mathlib artifacts reused.',
      'toolchain':query('lean','--version'),'source_sha256':{m:sha(p)for m,p in sources.items()},
      'source_paths':{m:str(p.relative_to(WORK)) for m,p in sources.items()},
      'verifier_sha256':sha(Path(__file__)),'steps':[],'axioms':{},
      'lake_manifest_sha256':sha(BASE/'lake-manifest.json')}
    def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(label,args,cwd,renv,negative=False):
        start=time.monotonic()
        with (logs/(label+'.log')).open('w')as out:
            p=subprocess.run(args,cwd=cwd,env=renv,stdout=out,stderr=subprocess.STDOUT,timeout=600)
        ok=p.returncode!=0 if negative else p.returncode==0
        report['steps'].append({'label':label,'exit_code':p.returncode,'passed':ok,
          'expected':'rejection'if negative else'success','seconds':time.monotonic()-start,'log_sha256':sha(logs/(label+'.log'))})
        save();print(label,p.returncode,flush=True)
        assert ok,label
    with tempfile.TemporaryDirectory(prefix='fresh-',dir=HERE/'build')as tmp:
        root=Path(tmp);renv=env.copy();renv['LEAN_PATH']=str(root)+':'+dep
        renv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
        names=[]
        for m,p in sources.items():
            shutil.copy2(p,root/p.name)
            if m in MODULES:
                source=p.read_text()
                assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/--.*?-/|--[^\n]*','',source,flags=re.S)),m
                ns=re.search(r'^namespace (\S+)',source,re.M).group(1)
                names.extend(ns+'.'+n for n in re.findall(r'^(?:theorem|lemma) (\w+)',source,re.M))
            run('build-'+m,[lean,'--root='+str(root),'-o',str(root/(m+'.olean')),str(root/p.name)],root,renv)
        (root/'Audit.lean').write_text('\n'.join(['import '+m for m in MODULES]+['#print axioms '+n for n in names])+'\n')
        run('axiom-audit',[lean,str(root/'Audit.lean')],root,renv)
        for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
            axioms={x.strip()for x in raw.split(',')if x.strip()};assert axioms<=ALLOWED,(name,axioms)
            report['axioms'][name]=sorted(axioms)
        assert set(report['axioms'])==set(names),(set(names)-set(report['axioms']))
        for m in MODULES:run('kernel-'+m,[checker,m,'-v'],root,renv)
        source=(root/'QuadraticSlowFilter.lean').read_text()
        old='theorem endpoint8 (x : Vector) : dEnergy 8 x ≤ -(1/2)*normSq x := by'
        assert source.count(old)==1
        (root/'FalseMargin.lean').write_text(source.replace(old,'theorem endpoint8 (x : Vector) : dEnergy 8 x ≤ -100*normSq x := by'))
        run('reject-false-mu-100',[lean,str(root/'FalseMargin.lean')],root,renv,negative=True)
        log=(logs/'reject-false-mu-100.log').read_text()
        assert ('linarith failed' in log or 'nlinarith failed' in log) and 'error: unknown' not in log
        report['negative_control_reason']='At r=8, x=(1,0,0,0), -dEnergy=1144/25<100. The false mu=100 margin cannot hold. false_stronger_margin_witness is proved in the accepted source.'
    report['source_unchanged']=all(sha(p)==report['source_sha256'][m]for m,p in sources.items())
    report['audited_statement_names']=names
    report['passed']=report['source_unchanged']and all(s['passed']for s in report['steps'])
    save();print(json.dumps({'passed':report['passed'],'audited_statements':len(names)}))
if __name__=='__main__':main()
