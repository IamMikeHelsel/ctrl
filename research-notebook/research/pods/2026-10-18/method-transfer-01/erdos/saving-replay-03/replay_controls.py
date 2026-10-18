#!/usr/bin/env python3
"""Fresh semantic controls using an already freshly verified saving build."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,shutil,subprocess,tempfile,time

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lean-controls').is_dir())
BIN=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
allowed={'propext','Classical.choice','Quot.sound'}
records=[]
for path in HERE.glob('unchanged-435-*/verification.json'):
    entry=json.loads(path.read_text())
    if entry.get('passed'):records.append((entry['completed_utc'],path,entry))
assert records,'Run replay.py successfully first'
_,manifest,data=max(records)
dep=manifest.parent
for src in data['source'].values():
    assert hashlib.sha256((HERE/src['copied']).read_bytes()).hexdigest()==src['sha256']
work=Path(tempfile.mkdtemp(prefix='controls-final-',dir=HERE))
shutil.copyfile(HERE/'MeaningfulControls.lean',work/'MeaningfulControls.lean')
cache=ROOT/'lean-controls/.lake/packages'
deps=sorted(p/'.lake/build/lib/lean' for p in cache.iterdir() if (p/'.lake/build/lib/lean').is_dir())
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[work,dep,*deps]))
result={'started_utc':datetime.now(timezone.utc).isoformat(),'work':str(work.relative_to(HERE)),
  'dependency_manifest':str(manifest.relative_to(HERE)),
  'dependency_manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),
  'lean_path':env['LEAN_PATH'],'runs':[]}

def save():
    (work/'verification.json').write_text(json.dumps(result,indent=2)+'\n')

def run(label,cmd):
    started=time.monotonic()
    proc=subprocess.run(cmd,cwd=work,env=env,text=True,capture_output=True,timeout=240)
    output=proc.stdout+proc.stderr
    (work/(label+'.log')).write_text(output)
    result['runs'].append({'label':label,'command':cmd,'exit':proc.returncode,
                          'seconds':time.monotonic()-started,'log':label+'.log'})
    save();print(label,proc.returncode,flush=True)
    return proc.returncode,output

code,out=run('compile-controls',[str(BIN/'lean'),'-o','MeaningfulControls.olean','MeaningfulControls.lean'])
assert code==0,out
axes={name:[x.strip() for x in values.split(',') if x.strip()]
      for name,values in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
assert len(axes)==4 and all(set(v)<=allowed for v in axes.values()),axes
result['axioms']=axes
code,out=run('kernel-controls',[str(BIN/'leanchecker'),'MeaningfulControls','-v'])
assert code==0,out

prefix='import MeaningfulControls\nopen Erdos128 SavingReplayControls\nopen scoped BigOperators\nnoncomputable section\n'
mutants={
 'NoTriangle':prefix+'''example : (1 / 18 : ℚ) ≤
    weightedObjective triangle thirds (fun _ => 0) (fun _ => (1 / 2 : ℚ)) -
      4 * savingLQ (1 / 2) * edgeMass triangle thirds ^ 3 := by
  rw [triangle_budget]
  norm_num
''',
 'BadNormalization':prefix+'''def invalidWeights : RatProbabilityWeight (Fin 2) where
  weight := fun _ => 1
  positive := by intro v; norm_num
  sum_eq_one := by norm_num
''',
 'NoActualSaving':prefix+'''example :
    weightedObjective edge halves (fun _ => 0) (fun _ => (1 / 2 : ℚ)) ≤
      weightedObjective edge halves (fun _ => 0) (fun _ => (1 / 2 : ℚ)) -
        4 * savingLQ (1 / 2) * edgeMass edge halves ^ 3 := by
  classical
  norm_num [weightedObjective, edge, halves, weightedMean, edgeMass,
    weightedDegree, savingLQ, centerRadiusQ,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Finset.filter_ne,
    Fin.sum_univ_succ]
'''}
result['negative_controls']=[]
for name,source in mutants.items():
    (work/(name+'.lean')).write_text(source)
    code,out=run('reject-'+name,[str(BIN/'lean'),name+'.lean'])
    assert code!=0 and 'unsolved goals' in out and 'Unknown' not in out,(name,out)
    result['negative_controls'].append({'name':name,'rejected':True,'reason':'well-typed false arithmetic/normalization goal remains unsolved'})
result['passed']=True;result['completed_utc']=datetime.now(timezone.utc).isoformat();save()
print(json.dumps({'passed':True,'work':str(work),'negative_controls':3}),flush=True)
