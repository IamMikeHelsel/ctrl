#!/usr/bin/env python3
"""Extend this reviewer's fresh closure with independently copied data/bridge modules."""
from pathlib import Path
import os,json,re,hashlib,shutil,subprocess,sys,time
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5];BASE=WORK/'lean-controls'
BUILD=HERE/'build';LOGS=HERE/'logs';BIND=HERE.parent/'bindings'
TARGETS=sys.argv[1:] or ['NativeData','NativeBridge','NativeInstances']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
baseline_file=HERE/'proof-review.json';baseline=json.loads(baseline_file.read_text());assert baseline['passed']
for m,p in baseline['source_paths'].items():
    assert sha(WORK/p)==baseline['source_hashes'][m]
    assert sha(BUILD/(m.replace('.','/')+'.lean'))==baseline['source_hashes'][m]
objects={m:sha(BUILD/(m.replace('.','/')+'.olean')) for m in baseline['source_paths']}
sources={m:BIND/(m+'.lean') for m in TARGETS}
for m,p in sources.items():assert p.exists(),p
report={'passed':False,'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
  'fresh_closure_report_sha256':sha(baseline_file),'fresh_closure_object_hashes':objects,
  'source_hashes':{m:sha(p) for m,p in sources.items()},'steps':[]}
def save():(HERE/'integration-review.json').write_text(json.dumps(report,indent=2)+'\n')
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
assert subprocess.check_output([lean,'--version'],text=True).strip()==baseline['toolchain']
assert sha(BASE/'lake-manifest.json')==baseline['lake_manifest_sha256']
env['LEAN_PATH']=':'.join([str(BUILD)]+baseline['external_cache_paths'])
env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
def run(label,args,negative=False):
    start=time.monotonic();p=LOGS/(label+'.log')
    with p.open('w') as out:r=subprocess.run(args,cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
    ok=r.returncode!=0 if negative else r.returncode==0
    report['steps'].append({'label':label,'exit_code':r.returncode,'passed':ok,
       'expected':'reject' if negative else 'pass','seconds':time.monotonic()-start,'log_sha256':sha(p)})
    save();print(label,r.returncode,flush=True);assert ok,label
public=dict(baseline['public_theorems']);available=set(public)
for m,p in sources.items():
    raw=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw),p
    for im in re.findall(r'^(?:public )?import (\S+)',raw,re.M):
        assert im.startswith('Mathlib.') or im in available,(m,im)
    ns=re.findall(r'^namespace (\S+)',raw,re.M);assert len(ns)==1,(m,ns)
    public[m]=[]
    for line in raw.splitlines():
        mat=re.match(r'^\s*(.*?)\b(?:theorem|lemma)\s+([^\s{(:]+)',line)
        if mat and not re.search(r'\bprivate\b',mat.group(1)):public[m].append(ns[0]+'.'+mat.group(2))
    dst=BUILD/(m+'.lean');shutil.copy2(p,dst);assert sha(dst)==report['source_hashes'][m]
    run('integration-build-'+m,[lean,'--root='+str(BUILD),'-o',str(dst.with_suffix('.olean')),str(dst)])
    available.add(m)
names=[n for group in public.values() for n in group];assert len(names)==len(set(names))
(BUILD/'IntegrationAudit.lean').write_text('\n'.join('import '+t for t in TARGETS+['HandoffWitnesses','ReviewWitnesses'])+'\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
run('integration-public-axioms',[lean,str(BUILD/'IntegrationAudit.lean')])
parsed={}
for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOGS/'integration-public-axioms.log').read_text()):
    ax={x.strip() for x in raw.split(',') if x.strip()};assert ax<={'propext','Classical.choice','Quot.sound'},(name,ax)
    parsed[name]=sorted(ax)
for name in re.findall(r"'([^']+)' does not depend on any axioms",(LOGS/'integration-public-axioms.log').read_text()):parsed[name]=[]
assert set(parsed)==set(names)
report['axioms']=parsed;report['public_theorems']=public;save()
for m in TARGETS:run('integration-kernel-'+m,[str(Path(lean).with_name('leanchecker')),m,'-v'])
control='''import NativeData
namespace IndependentNativeDataReview
open NativeRational
def changedJoin : List Piece := match hold_jitter__ruckig with
  | s::t::rest => s::{t with p := t.p+1/1000}::rest
  | xs => xs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem changed_join_is_rejected : check (5/2) changedJoin = false := by decide +kernel
end IndependentNativeDataReview
'''
(BUILD/'NativeMutation.lean').write_text(control)
(HERE/'NativeMutation.lean').write_text(control)
run('changed-join-counterexample',[lean,'--root='+str(BUILD),'-o',str(BUILD/'NativeMutation.olean'),str(BUILD/'NativeMutation.lean')])
run('kernel-NativeMutation',[str(Path(lean).with_name('leanchecker')),'NativeMutation','-v'])
false=control.replace('changed_join_is_rejected','false_acceptance').replace('changedJoin = false','changedJoin = true')
(BUILD/'FalseNativeJoin.lean').write_text(false)
run('reject-altered-native-join',[lean,str(BUILD/'FalseNativeJoin.lean')],True)
false_log=(LOGS/'reject-altered-native-join.log').read_text();assert 'unknown' not in false_log and 'false' in false_log
assert sha(baseline_file)==report['fresh_closure_report_sha256']
assert all(sha(WORK/p)==baseline['source_hashes'][m] for m,p in baseline['source_paths'].items())
assert all(sha(BUILD/(m.replace('.','/')+'.olean'))==h for m,h in objects.items())
assert all(sha(p)==report['source_hashes'][m] for m,p in sources.items())
report['all_sources_and_baseline_objects_unchanged']=True;report['passed']=True
report['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime());save()
print(json.dumps({'passed':True,'total_local_modules':len(public),'total_public_axioms':len(names),
 'new_module_statement_counts':{m:len(public[m]) for m in TARGETS}}),flush=True)
