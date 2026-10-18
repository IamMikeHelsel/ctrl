#!/usr/bin/env python3
"""Final absolute-time composition and complete target/control axiom audit."""
from pathlib import Path
import os,json,re,hashlib,shutil,subprocess,time
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5];BASE=WORK/'lean-controls'
BUILD=HERE/'build';LOGS=HERE/'logs';BUILDER=HERE.parent/'builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((HERE/'proof-review.json').read_text());cov=json.loads((HERE/'coverage-review.json').read_text())
assert base['passed'] and cov['passed']
src=BUILDER/'NativeGlobal.lean'
assert sha(src)=='ef99ea5638863587fb26eb25e6bbecb87851cd1e16ce95495cc10abc65804572'
assert sha(BUILDER/'global-source-freeze.json')=='e33f00f47d70c3ed0af55f9bb68b135e3c998f5e8c448228a830f1dfc8a3bbf1'
objects={str(p.relative_to(BUILD)):sha(p) for p in BUILD.rglob('*.olean')}
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lean=subprocess.check_output([str(WORK/'.tools/elan/bin/lake'),'env','which','lean'],cwd=BASE,env=env,text=True).strip()
env['LEAN_PATH']=':'.join([str(BUILD)]+base['external_cache_paths']);env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
report={'passed':False,'coverage_review_sha256':sha(HERE/'coverage-review.json'),
 'global_source_sha256':sha(src),'global_freeze_sha256':sha(BUILDER/'global-source-freeze.json'),
 'prior_object_hashes':objects,'steps':[]}
def save():(HERE/'global-review.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args):
 start=time.monotonic();log=LOGS/(label+'.log')
 with log.open('w') as out:r=subprocess.run(args,cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
 report['steps'].append({'label':label,'passed':r.returncode==0,'exit_code':r.returncode,
  'seconds':time.monotonic()-start,'log_sha256':sha(log)})
 save();print(label,r.returncode,flush=True);assert r.returncode==0,label
raw=re.sub(r'/-.*?-/|--[^\n]*','',src.read_text(),flags=re.S)
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw)
assert re.findall(r'^import (\S+)',raw,re.M)==['NativeCoverage']
shutil.copy2(src,BUILD/'NativeGlobal.lean')
run('global-build',[lean,'--root='+str(BUILD),'-o',str(BUILD/'NativeGlobal.olean'),str(BUILD/'NativeGlobal.lean')])
names=list(cov['axioms'])+['NativeRational.checked_absolute_position_tracking',
 'IndependentNativeDataReview.changed_join_is_rejected',
 'IndependentCoverageReview.enlarged_horizon_is_rejected',
 'IndependentCoverageReview.missing_initial_interval_is_rejected']
(BUILD/'FinalAudit.lean').write_text('import NativeGlobal\nimport NativeInstances\nimport HandoffWitnesses\nimport ReviewWitnesses\nimport NativeMutation\nimport CoverageWitnesses\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
run('final-public-axioms',[lean,str(BUILD/'FinalAudit.lean')])
parsed={}
for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOGS/'final-public-axioms.log').read_text()):
 ax={x.strip() for x in raw.split(',') if x.strip()};assert ax<={'propext','Classical.choice','Quot.sound'};parsed[name]=sorted(ax)
for name in re.findall(r"'([^']+)' does not depend on any axioms",(LOGS/'final-public-axioms.log').read_text()):parsed[name]=[]
assert set(parsed)==set(names);report['axioms']=parsed;save()
run('global-kernel',[str(Path(lean).with_name('leanchecker')),'NativeGlobal','-v'])
assert sha(src)==report['global_source_sha256']
assert all(sha(BUILD/p)==h for p,h in objects.items())
report['all_sources_and_prior_objects_unchanged']=True;report['passed']=True
report['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());save()
print(json.dumps({'passed':True,'audited_public_statements':len(parsed),'fresh_local_modules_including_controls':len(objects)+1}),flush=True)
