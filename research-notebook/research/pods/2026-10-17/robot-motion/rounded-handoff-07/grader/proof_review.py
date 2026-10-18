#!/usr/bin/env python3
"""Independent copied-source rebuild, full local public-axiom audit and kernel replay."""
from pathlib import Path
import os, re, json, hashlib, shutil, subprocess, time, sys
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[5]; BASE=WORK/'lean-controls'; BUILDER=HERE.parent/'builder'; BIND=HERE.parent/'bindings'
TARGETS=sys.argv[1:] or ['RoundedHandoff','ReviewWitnesses']
BUILD=HERE/'build'; LOGS=HERE/'logs'; BUILD.mkdir(exist_ok=True);LOGS.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
extra={m:WORK/p for m,p in {
 'ComparisonEnvelope':'research/adjacent-controls/variable-response/ComparisonEnvelope.lean',
 'RobustHold':'research/adjacent-controls/variable-response/sampled-handoff/RobustHold.lean',
 'SmoothReplan':'research/adjacent-controls/vla-smooth-replanning/SmoothReplan.lean',
 'TrackingReplan':'research/adjacent-controls/tracking-replans/TrackingReplan.lean',
 'ScaledTracking':'research/adjacent-controls/tracking-replans/ScaledTracking.lean'}.items()}
for folder in (BUILDER,BIND,HERE):
    for p in folder.glob('*.lean'):extra[p.stem]=p
sources={}
def visit(m):
    if m in sources or m.startswith('Mathlib.') or m.startswith('Lean.'):return
    p=extra.get(m,BASE/(m.replace('.','/')+'.lean'))
    assert p.exists(),(m,p)
    for im in re.findall(r'^(?:public )?import (\S+)',p.read_text(),re.M):visit(im)
    sources[m]=p
for t in TARGETS:visit(t)
report={'passed':False,'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
 'targets':TARGETS,'source_paths':{m:str(p.relative_to(WORK)) for m,p in sources.items()},
 'source_hashes':{m:sha(p) for m,p in sources.items()},'steps':[]}
def save():(HERE/'proof-review.json').write_text(json.dumps(report,indent=2)+'\n')
public={}
for m,p in sources.items():
    raw=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw),p
    ns=re.findall(r'^namespace (\S+)',raw,re.M);assert len(ns)==1,(m,ns)
    names=[]
    for line in raw.splitlines():
        match=re.match(r'^\s*(.*?)\b(?:theorem|lemma)\s+([^\s{(:]+)',line)
        if match and not re.search(r'\bprivate\b',match.group(1)):names.append(ns[0]+'.'+match.group(2))
    public[m]=names
report['public_theorems']=public;allnames=[n for names in public.values() for n in names]
assert len(set(allnames))==len(allnames)
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
paths=[p for p in paths if Path(p).resolve()!=(BASE/'.lake/build/lib/lean').resolve()]
report['toolchain']=subprocess.check_output([lean,'--version'],env=env,text=True).strip()
report['lean_toolchain']=(BASE/'lean-toolchain').read_text().strip()
report['lake_manifest_sha256']=sha(BASE/'lake-manifest.json')
report['mathlib_pinned_revision']=next(x['rev'] for x in json.loads((BASE/'lake-manifest.json').read_text())['packages'] if x['name']=='mathlib')
report['external_cache_paths']=paths
assert report['lean_toolchain']=='leanprover/lean4:v4.35.0'
assert report['mathlib_pinned_revision']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
env['LEAN_PATH']=':'.join([str(BUILD)]+paths)
env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
def run(label,args,negative=False):
    t=time.monotonic(); log=LOGS/(label+'.log')
    with log.open('w') as out:
        p=subprocess.run(args,cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
    ok=p.returncode!=0 if negative else p.returncode==0
    report['steps'].append({'label':label,'exit_code':p.returncode,'expected':'reject' if negative else 'pass',
      'passed':ok,'seconds':time.monotonic()-t,'log_sha256':sha(log)})
    save();print(label,p.returncode,flush=True);assert ok,label
for m,p in sources.items():
    dst=BUILD/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(p,dst);assert sha(dst)==report['source_hashes'][m]
    run('build-'+m,[lean,'--root='+str(BUILD),'-o',str(dst.with_suffix('.olean')),str(dst)])
(BUILD/'ReviewAudit.lean').write_text('\n'.join('import '+t for t in TARGETS)+'\n'+ '\n'.join('#print axioms '+n for n in allnames)+'\n')
run('public-axioms',[lean,str(BUILD/'ReviewAudit.lean')])
parsed={}
for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOGS/'public-axioms.log').read_text()):
    ax={x.strip() for x in raw.split(',') if x.strip()};assert ax<={'propext','Classical.choice','Quot.sound'},(name,ax)
    parsed[name]=sorted(ax)
# Lean prints axiom-free declarations using a separate format.
for name in re.findall(r"'([^']+)' does not depend on any axioms",(LOGS/'public-axioms.log').read_text()):parsed[name]=[]
assert set(parsed)==set(allnames),(set(allnames)-set(parsed),set(parsed)-set(allnames))
report['axioms']=parsed;save()
for m in dict.fromkeys(['RobustHold','TrackingReplan','ScaledTracking']+TARGETS):
    if m in sources:run('kernel-'+m,[checker,m,'-v'])
if 'ReviewWitnesses' in TARGETS:
    controls={
      'missing-jump-reserve':'''example : ∀ i, |coordinates 0 (scaledError 10 zeroPath velocityJump 0) i| ≤ 0 := by
  intro i
  fin_cases i <;> norm_num [coordinates, scaledError, scaleState, LeanControls.TrackingReplan.error, zeroPath, velocityJump]
''',
      'radius-reset':'''example : |coordinates 0 (scaledError 10 negativeUnitPath unitPath 0) 0| ≤ (1:ℝ) := by
  norm_num [coordinates, scaledError, scaleState, LeanControls.TrackingReplan.error, negativeUnitPath, unitPath]
''',
      'missing-physical-match':'''example : ∀ i, |coordinates 0 (scaledError 10 unitPath zeroPath 0) i| ≤ 0 := by
  intro i
  fin_cases i <;> norm_num [coordinates, scaledError, scaleState, LeanControls.TrackingReplan.error, zeroPath, unitPath]
'''}
    for label,body in controls.items():
        p=BUILD/('False_'+label.replace('-','_')+'.lean')
        p.write_text('import ReviewWitnesses\nopen IndependentRoundedReview LeanControls.RobustHold LeanControls.ScaledTracking\n'+body)
        run('reject-'+label,[lean,str(p)],True)
        log=(LOGS/('reject-'+label+'.log')).read_text()
        assert 'unsolved goals' in log and 'unknown' not in log,label
assert all(sha(p)==report['source_hashes'][m] for m,p in sources.items())
report['all_sources_unchanged']=True;report['passed']=True
report['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
save();print(json.dumps({'passed':True,'modules':len(sources),'public_axiom_count':len(allnames)}),flush=True)
