#!/usr/bin/env python3
"""Independent check of absolute-time coverage against the already checked closure."""
from pathlib import Path
import os,json,re,hashlib,shutil,subprocess,time
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5];BASE=WORK/'lean-controls'
BUILD=HERE/'build';LOGS=HERE/'logs';BUILDER=HERE.parent/'builder';BIND=HERE.parent/'bindings'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((HERE/'proof-review.json').read_text());integ=json.loads((HERE/'integration-review.json').read_text())
assert base['passed'] and integ['passed']
source=BUILDER/'NativeCoverage.lean'
assert sha(source)=='cefedece374064f5a579effcf39a8c9e7836bba7bc917ed84323c75b52da05c4'
assert sha(BUILDER/'coverage-source-freeze.json')=='048ce28b392571e8e9bb56bf840c10b537284f61986b3aa7e2f8271126dc886c'
for m,p in base['source_paths'].items():assert sha(WORK/p)==base['source_hashes'][m]
for m,h in integ['source_hashes'].items():assert sha(BIND/(m+'.lean'))==h
objects={m:sha(BUILD/(m.replace('.','/')+'.olean')) for m in integ['public_theorems']}
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lean=subprocess.check_output([str(WORK/'.tools/elan/bin/lake'),'env','which','lean'],cwd=BASE,env=env,text=True).strip()
env['LEAN_PATH']=':'.join([str(BUILD)]+base['external_cache_paths']);env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
report={'passed':False,'integration_review_sha256':sha(HERE/'integration-review.json'),
 'coverage_source_sha256':sha(source),'source_freeze_sha256':sha(BUILDER/'coverage-source-freeze.json'),
 'prior_object_hashes':objects,'steps':[]}
def save():(HERE/'coverage-review.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args,negative=False):
 t=time.monotonic();p=LOGS/(label+'.log')
 with p.open('w') as out:r=subprocess.run(args,cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
 ok=(r.returncode!=0) if negative else (r.returncode==0)
 report['steps'].append({'label':label,'passed':ok,'expected':'reject' if negative else 'pass',
  'exit_code':r.returncode,'seconds':time.monotonic()-t,'log_sha256':sha(p)})
 save();print(label,r.returncode,flush=True);assert ok,label
raw=re.sub(r'/-.*?-/|--[^\n]*','',source.read_text(),flags=re.S)
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw)
assert re.findall(r'^import (\S+)',raw,re.M)==['NativeBridge']
names=['NativeRational.'+n for n in re.findall(r'^(?:@\[simp\] )?theorem (\S+)',raw,re.M)]
assert len(names)==5
dst=BUILD/'NativeCoverage.lean';shutil.copy2(source,dst)
run('coverage-build',[lean,'--root='+str(BUILD),'-o',str(dst.with_suffix('.olean')),str(dst)])
allnames=list(integ['axioms'])+names
(BUILD/'CoverageAudit.lean').write_text('import NativeCoverage\nimport NativeInstances\nimport HandoffWitnesses\nimport ReviewWitnesses\n'+'\n'.join('#print axioms '+n for n in allnames)+'\n')
run('coverage-public-axioms',[lean,str(BUILD/'CoverageAudit.lean')])
parsed={}
for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOGS/'coverage-public-axioms.log').read_text()):
 ax={x.strip() for x in raw.split(',') if x.strip()};assert ax<={'propext','Classical.choice','Quot.sound'};parsed[name]=sorted(ax)
for name in re.findall(r"'([^']+)' does not depend on any axioms",(LOGS/'coverage-public-axioms.log').read_text()):parsed[name]=[]
assert set(parsed)==set(allnames);report['axioms']=parsed;save()
checker=str(Path(lean).with_name('leanchecker'))
run('coverage-kernel',[checker,'NativeCoverage','-v'])
controls='''import NativeCoverage
namespace IndependentCoverageReview
open NativeRational
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem enlarged_horizon_is_rejected : check 3 hold_jitter__ruckig = false := by decide +kernel
theorem missing_initial_interval_is_rejected : check (5/2) (hold_jitter__ruckig.drop 1) = false := by decide +kernel
end IndependentCoverageReview
'''
(HERE/'CoverageWitnesses.lean').write_text(controls);(BUILD/'CoverageWitnesses.lean').write_text(controls)
run('coverage-positive-controls',[lean,'--root='+str(BUILD),'-o',str(BUILD/'CoverageWitnesses.olean'),str(BUILD/'CoverageWitnesses.lean')])
run('coverage-controls-kernel',[checker,'CoverageWitnesses','-v'])
false=controls.replace('enlarged_horizon_is_rejected','false_extended_acceptance').replace('check 3 hold_jitter__ruckig = false','check 3 hold_jitter__ruckig = true')
(BUILD/'FalseHorizon.lean').write_text(false)
run('reject-enlarged-horizon',[lean,str(BUILD/'FalseHorizon.lean')],True)
assert 'unknown' not in (LOGS/'reject-enlarged-horizon.log').read_text()
assert sha(source)==report['coverage_source_sha256']
assert all(sha(BUILD/(m.replace('.','/')+'.olean'))==h for m,h in objects.items())
report['new_coverage_theorems']=names;report['all_sources_and_prior_objects_unchanged']=True
report['passed']=True;report['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());save()
print(json.dumps({'passed':True,'audited_public_statements':len(parsed),'local_modules':len(objects)+1}),flush=True)
