#!/usr/bin/env python3
"""Finish reviewer checks after an isolated type annotation repair in its fixture.

The frozen 42-module rebuild and eight target replays passed in verification.json.
Only the reviewer fixture failed, because an untyped rational vector was inferred
as naturals. Preserve that failure. Reuse the freshly built and already replayed
closure and rerun the corrected reviewer source and its dependent checks.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4];BASE=WORK/'lean-controls';BUILD=HERE/'build';BUILDER=HERE.parent/'builder-01'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((HERE/'verification.json').read_text())
assert len([s for s in old['steps'] if s['label'].startswith('build-')])==42
assert len([s for s in old['steps'] if s['label'].startswith('kernel-')])==8
assert all(s['passed'] for s in old['steps'] if s['label']!='review-ReviewWitnesses')
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
env['LEAN_PATH']=old['lean_path'];env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
report={'passed':False,'closure_verification_sha256':sha(HERE/'verification.json'),'closure_modules':42,'closure_public_statements':len(old['public_statements']),'closure_kernel_replays':8,'isolated_development_failure':'Reviewer constant-vector type inferred as naturals. Explicit State annotation repairs it. No frozen source changed. Initial failure retained in review-attempt-01.','steps':[]}
def save():(HERE/'final-verification.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args,negative=False):
    p=HERE/'logs'/(label+'.log');start=time.monotonic()
    with p.open('w') as out: proc=subprocess.run(args,cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=360)
    ok=(proc.returncode!=0) if negative else (proc.returncode==0)
    report['steps'].append({'label':label,'exit_code':proc.returncode,'expected':'rejection' if negative else 'success','passed':ok,'seconds':time.monotonic()-start,'log_sha256':sha(p)})
    save();print(label,proc.returncode,flush=True);assert ok,label
    return p.read_text()
source=HERE/'ReviewWitnesses.lean';target=BUILD/source.name;shutil.copy2(source,target)
run('review-fixtures-final',[lean,'--root='+str(BUILD),'-o',str(target.with_suffix('.olean')),str(target)])
run('review-fixtures-kernel-final',[str(Path(lean).with_name('leanchecker')),'ReviewWitnesses','-v'])
run('review-fixtures-axioms-final',['python3',str(HERE/'audit_review.py')])
report['reviewer_axioms_sha256']=sha(HERE/'reviewer-axioms.json')
for p in sorted((HERE/'negative').glob('*.lean')):
    target=BUILD/p.name;shutil.copy2(p,target)
    raw=run('reject-'+p.stem,[lean,str(target)],negative=True)
    assert ('unsolved goals' in raw or 'linarith failed' in raw),p
    assert not any(w in raw.lower() for w in ['unknown identifier','unknown module','timeout','maximum recursion','maximum number of heartbeats']),p
report['closure_source_unchanged']=all(sha(WORK/old['source_path'][m])==s for m,s in old['source_sha256'].items())
artifacts=json.loads((BUILDER/'artifact-sha256.json').read_text())
report['builder_artifacts_unchanged']=all(sha(BUILDER/p)==s for p,s in artifacts.items())
report['review_source_sha256']=sha(source)
report['passed']=report['closure_source_unchanged'] and report['builder_artifacts_unchanged'] and all(s['passed'] for s in report['steps'])
save();print(json.dumps({'passed':report['passed'],'negative_controls':len(list((HERE/'negative').glob('*.lean')))}))
