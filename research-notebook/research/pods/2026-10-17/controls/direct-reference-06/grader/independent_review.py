#!/usr/bin/env python3
"""Independent semantic binding, fresh compilation, kernel replay, and mutations.
The review does not import the builder's Python code or write builder artifacts.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,os,re,shutil,subprocess,tempfile,time
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[5]
BUILDER=HERE.parent/'builder'
COMPARE=HERE.parent.parent/'causal-stop-05/builder'
BASE=WORK/'lean-controls'
LOGS=HERE/'logs';LOGS.mkdir(exist_ok=True)
BUILD=HERE/'build';BUILD.mkdir(exist_ok=True)
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def frozen(p):
    manifest=json.loads((p/'artifact-sha256.json').read_text())
    assert all(sha(p/n)==v for n,v in manifest.items()),p
    return {'manifest_sha256':sha(p/'artifact-sha256.json'),'files':manifest}
report={'passed':False,'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        'before':{'builder':frozen(BUILDER),'comparison':frozen(COMPARE)},'steps':[]}
assert report['before']['builder']['manifest_sha256']=='54cb026c13244b788b85594803eff0bb31782ac76b825f3dbb8b4d23a2d1fc20'
assert report['before']['comparison']['manifest_sha256']=='424d723ecff3b672f04fc74f4495f06f8306c6dbf401dd03ebe47f8b0d88980d'
def save(): (HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')

def independent_reference_check():
    ref=json.loads((COMPARE/'reference.json').read_text())
    raw=(BUILDER/'FrozenReference.lean').read_text()
    tables={}
    for name in ['phaseStart','duration','position']:
        block=raw.split('def '+name+' :',1)[1].split('\n\n',1)[0]
        tables[name]={int(k):v.strip() for k,v in re.findall(r'^  \| (\d+) => (.+)$',block,re.M)}
    def value(s):return Q(s.strip().strip('()'))
    def coeffs(s):
        d={}
        for term in s.split(' + '):
            m=re.fullmatch(r'C ([^*]+?)(?: \* X(?:\^(\d+))?)?',term)
            assert m,term
            power=int(m.group(2) or 1) if '* X' in term else 0
            d[power]=value(m.group(1))
        return [d.get(i,Q(0)) for i in range(max(d)+1)]
    def trim(a):
        a=list(a)
        while len(a)>1 and a[-1]==0:a.pop()
        return a
    def der(a):return [i*x for i,x in enumerate(a)][1:] or [Q(0)]
    def ev(a,x):return sum(c*x**i for i,c in enumerate(a))
    rows=[];last=None
    for k,p in enumerate(ref):
        cs=coeffs(tables['position'][k]);expected=list(map(Q,p['position_coefficients_local_time']))
        start,end=Q(p['start']),Q(p['end']);duration=end-start
        assert trim(cs)==trim(expected)
        assert value(tables['phaseStart'][k])==start
        assert value(tables['duration'][k])==duration>0
        ds=[cs]
        for _ in range(3):ds.append(der(ds[-1]))
        beginning=[ev(d,Q(0)) for d in ds];finish=[ev(d,duration) for d in ds]
        if last is not None:assert beginning==last
        last=finish
        rows.append({'k':k,'start':str(start),'end':str(end),'initial_q_v_a_j':list(map(str,beginning)),'final_q_v_a_j':list(map(str,finish))})
    assert len(rows)==8 and rows[0]['initial_q_v_a_j']==['0','0','0','10']
    assert rows[-1]['final_q_v_a_j']==['3/5','0','0','0'] and rows[-1]['end']=='3/2'
    assert Q(1,100)+Q(10,480)<=2*100*Q(1,5000)
    return {'phases':rows,'exact_polynomials_and_times_match':True,'all_q_v_a_j_joins_match':True,
            'coefficient_feedforward':str(Q(5,48*10)), 'budget_lhs':str(Q(1,100)+Q(10,480)),
            'budget_rhs':str(Q(1,25))}
report['independent_reference']=independent_reference_check();save()
EXTRA={m:WORK/p for m,p in {
 'ComparisonEnvelope':'research/adjacent-controls/variable-response/ComparisonEnvelope.lean',
 'RobustHold':'research/adjacent-controls/variable-response/sampled-handoff/RobustHold.lean',
 'SmoothReplan':'research/adjacent-controls/vla-smooth-replanning/SmoothReplan.lean',
 'TrackingReplan':'research/adjacent-controls/tracking-replans/TrackingReplan.lean',
 'ScaledTracking':'research/adjacent-controls/tracking-replans/ScaledTracking.lean'}.items()}
EXTRA.update({m:BUILDER/(m+'.lean') for m in ['FrozenReference','DirectReference']})
sources={}
def visit(m):
    if m in sources:return
    if m.startswith('Mathlib.'):return
    p=EXTRA.get(m,BASE/(m.replace('.','/')+'.lean'))
    assert p.exists(),(m,p)
    for im in re.findall(r'^(?:public )?import (\S+)',p.read_text(),re.M):visit(im)
    sources[m]=p
visit('DirectReference')
report['source_paths']={m:str(p.relative_to(WORK)) for m,p in sources.items()}
report['source_hashes']={m:sha(p) for m,p in sources.items()}
public={}
for m,p in sources.items():
    raw=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw),p
    ns=re.findall(r'^namespace (\S+)',raw,re.M);assert len(ns)==1,(p,ns)
    names=[]
    for line in raw.splitlines():
        match=re.match(r'^\s*(.*?)\b(?:theorem|lemma)\s+([^\s{(:]+)',line)
        if match and not re.search(r'\bprivate\b',match.group(1)):names.append(ns[0]+'.'+match.group(2))
    public[m]=names
report['public_theorems']=public
allnames=[n for names in public.values() for n in names]
assert len(set(allnames))==len(allnames)
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=query('which','lean');checker=str(Path(lean).with_name('leanchecker'))
paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
# Remove the current package's compiled objects. Only external library cache paths remain.
local_cache=str((BASE/'.lake/build/lib/lean').resolve())
paths=[p for p in paths if str(Path(p).resolve())!=local_cache]
report['toolchain']=subprocess.check_output([lean,'--version'],env=env,text=True).strip()
report['mathlib_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=BASE/'.lake/packages/mathlib',text=True).strip()
report['lean_toolchain']=(BASE/'lean-toolchain').read_text().strip()
report['lake_manifest_sha256']=sha(BASE/'lake-manifest.json')
report['external_cache_paths']=paths
assert report['lean_toolchain']=='leanprover/lean4:v4.35.0'
assert report['mathlib_revision']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
def run(label,args,cwd,env,negative=False):
    t=time.monotonic();p=LOGS/(label+'.log')
    with p.open('w') as out:r=subprocess.run(args,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
    ok=(r.returncode!=0) if negative else (r.returncode==0)
    report['steps'].append({'label':label,'exit_code':r.returncode,'expected':'reject' if negative else 'pass','passed':ok,'seconds':time.monotonic()-t,'log_sha256':sha(p)})
    save();print(label,r.returncode,flush=True);assert ok,label
with tempfile.TemporaryDirectory(prefix='review-',dir=BUILD) as temp:
    root=Path(temp);renv=env.copy();renv['LEAN_PATH']=':'.join([str(root)]+paths)
    renv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    for m,p in sources.items():
        dest=root/(m.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
        assert sha(dest)==report['source_hashes'][m]
        run('build-'+m,[lean,'--root='+str(root),'-o',str(dest.with_suffix('.olean')),str(dest)],root,renv)
    (root/'ReviewAudit.lean').write_text('import DirectReference\n'+'\n'.join('#print axioms '+n for n in allnames)+'\n')
    run('public-axioms',[lean,str(root/'ReviewAudit.lean')],root,renv)
    parsed={}
    for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOGS/'public-axioms.log').read_text()):
        ax={x.strip() for x in raw.split(',') if x.strip()};assert ax<=ALLOWED,(name,ax);parsed[name]=sorted(ax)
    assert set(parsed)==set(allnames)
    report['axioms']=parsed;save()
    for m in ['RobustHold','TrackingReplan','ScaledTracking','FrozenReference','DirectReference']:
        run('kernel-'+m,[checker,m,'-v'],root,renv)
    original=(root/'DirectReference.lean').read_text()
    old='    |jerk k t| ≤ 10 := by\n  interval_cases k';assert original.count(old)==1
    (root/'FalseJerk.lean').write_text(original.replace(old,'    |jerk k t| ≤ 9 := by\n  interval_cases k'))
    run('reject-jerk-nine',[lean,str(root/'FalseJerk.lean')],root,renv,True)
    log=(LOGS/'reject-jerk-nine.log').read_text();assert ('unsolved goals' in log or 'linarith failed' in log) and 'unknown' not in log
    changed=root/'changed';changed.mkdir()
    frozen_source=(root/'FrozenReference.lean').read_text();assert frozen_source.count('C (44217/1600000)')==1
    (changed/'FrozenReference.lean').write_text(frozen_source.replace('C (44217/1600000)','C (44218/1600000)'))
    shutil.copy2(root/'DirectReference.lean',changed/'DirectReference.lean')
    menv=renv.copy();menv['LEAN_PATH']=str(changed)+':'+renv['LEAN_PATH']
    run('changed-data-compiles',[lean,'--root='+str(changed),'-o',str(changed/'FrozenReference.olean'),str(changed/'FrozenReference.lean')],changed,menv)
    run('reject-changed-join',[lean,'--root='+str(changed),str(changed/'DirectReference.lean')],changed,menv,True)
    log=(LOGS/'reject-changed-join.log').read_text();assert 'unsolved goals' in log and 'unknown' not in log
    witness='''import DirectReference
open LeanControls.DirectReference LeanControls.ScaledTracking LeanControls.UncertainLag
example : ¬ |jerk 0 0| ≤ (9 : ℝ) := by rw [initial_jerk]; norm_num
example : (44218/1600000 : ℝ) ≠ reference 1 (duration 1) 0 := by
  norm_num [reference, duration, position]
example (f q : ℝ → State) (j : ℝ → ℝ) (t : ℝ) :
    physicalInput 10 f q j t = q t 2 - 800 * (f t 0 - q t 0) -
      60 * (f t 1 - q t 1) - (f t 2 - q t 2)/2 + j t/96 := by
  norm_num [physicalInput]
  ring
'''
    (HERE/'ReviewWitness.lean').write_text(witness);(root/'ReviewWitness.lean').write_text(witness)
    run('positive-review-witnesses',[lean,'--root='+str(root),'-o',str(root/'ReviewWitness.olean'),str(root/'ReviewWitness.lean')],root,renv)
    run('kernel-ReviewWitness',[checker,'ReviewWitness','-v'],root,renv)
report['after']={'builder':frozen(BUILDER),'comparison':frozen(COMPARE)}
assert report['after']==report['before']
assert all(sha(p)==report['source_hashes'][m] for m,p in sources.items())
report['all_source_hashes_unchanged']=True
report['passed']=True
report['finished_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
save()
print(json.dumps({'passed':True,'fresh_modules':len(sources),'audited_theorems':len(allnames),'target_theorems':len(public['DirectReference'])}),flush=True)
