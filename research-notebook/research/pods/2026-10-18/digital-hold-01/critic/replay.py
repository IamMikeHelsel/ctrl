#!/usr/bin/env python3
"""Independent frozen-packet replay. Writes only within critic/."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BUILDER=HERE.parent/'builder'
BASE=WORK/'lean-controls'
EXPECTED_MANIFEST='79f0478d50e4bbe346f964e3c2b737c2729b8287ff0734d476e9789ce449787c'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def verify_frozen():
    assert sha(BUILDER/'artifact-sha256.json')==EXPECTED_MANIFEST
    manifest=json.loads((BUILDER/'artifact-sha256.json').read_text())
    for f,h in manifest['files'].items():
        assert sha(BUILDER/f)==h,f
    return manifest
manifest=verify_frozen()
fresh=HERE/'fresh';fresh.mkdir(exist_ok=True)
assert not list(fresh.iterdir()),'Fresh replay directory must be empty'
logs=HERE/'replay-logs';logs.mkdir(exist_ok=True)
for n in ['DigitalHold.lean','DispatchWitness.lean','artifact-sha256.json','provenance.json','input-sha256.json']:
    shutil.copy2(BUILDER/n,fresh/n)
# Validate copied inherited fragments independently of the builder flag.
prov=json.loads((fresh/'provenance.json').read_text())
origin=WORK/prov['origin']; assert sha(origin)==prov['origin_sha256']
original=origin.read_text(); current=(fresh/'DigitalHold.lean').read_text()
for p in prov['copied_segments']:
    frag=original[original.index(p['start_marker']):original.index(p['end_marker_exclusive'])]
    assert hashlib.sha256(frag.encode()).hexdigest()==p['sha256']
    assert frag in current
for n in ['DigitalHold','DispatchWitness']:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',(fresh/(n+'.lean')).read_text())
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args): return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=Path(query('which','lean')); checker=lean.with_name('leanchecker')
paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
paths=[p for p in paths if '.lake/packages/' in p]
assert paths and all('lean-controls/.lake/build' not in p for p in paths)
env['LEAN_PATH']=str(fresh)+':'+':'.join(paths)
env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
report={'passed':False,'scope':'Independent fresh rebuild of both complete local source files; pinned Mathlib and its dependency artifacts reused. Separate leanchecker replay of both modules.',
 'frozen_manifest_sha256':EXPECTED_MANIFEST,'frozen_files_verified_before':len(manifest['files']),
 'source_sha256':{n:sha(fresh/(n+'.lean')) for n in ['DigitalHold','DispatchWitness']},
 'toolchain':query('lean','--version'),'lean_sha256':sha(lean),'leanchecker_sha256':sha(checker),
 'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),
 'mathlib_commit':subprocess.check_output(['git','-C',str(BASE/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),
 'mathlib_tracked_patch_sha256':hashlib.sha256(subprocess.check_output(['git','-C',str(BASE/'.lake/packages/mathlib'),'diff','--binary','HEAD'])).hexdigest(),
 'lean_path':env['LEAN_PATH'],'copied_geometry_validated':True,'steps':[],'axioms':{}}
def save(): (HERE/'replay-results.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args,negative=False):
    start=time.monotonic(); log=logs/(label+'.log')
    with log.open('w') as out:
        proc=subprocess.run(list(map(str,args)),cwd=fresh,env=env,stdout=out,stderr=subprocess.STDOUT)
    raw=log.read_text()
    passed=proc.returncode==0 if not negative else (proc.returncode!=0 and 'error:' in raw and ('unsolved goals' in raw or 'linarith failed' in raw) and 'unknown' not in raw.lower())
    report['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':proc.returncode,'passed':passed,
      'expected':'false mathematical goal rejected' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(log)})
    save(); print(label,proc.returncode,passed,flush=True)
    assert passed,label
names=[]
for n in ['DigitalHold','DispatchWitness']:
    p=fresh/(n+'.lean'); raw=p.read_text()
    namespace=re.search(r'^namespace (\S+)',raw,re.M).group(1)
    names += [namespace+'.'+x for x in re.findall(r'^theorem (\w+)',raw,re.M)]
    run('build-'+n,[lean,'--root='+str(fresh),'-o',fresh/(n+'.olean'),p])
(fresh/'Audit.lean').write_text('import DispatchWitness\n'+''.join('#print axioms '+n+'\n' for n in names))
run('axiom-audit',[lean,fresh/'Audit.lean'])
for name,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
    axioms={x.strip() for x in body.split(',') if x.strip()}
    assert axioms<=ALLOWED,(name,axioms)
    report['axioms'][name]=sorted(axioms)
assert set(report['axioms'])==set(names)
report['theorem_count']=len(names);save()
(fresh/'Statements.lean').write_text('import DispatchWitness\n'+''.join('#print '+n+'\n' for n in [
 'LeanControls.DigitalHold.Execution','LeanControls.DigitalHold.IsSchedule',
 'LeanControls.DigitalHold.IsSampledExecution','LeanControls.DigitalHold.prefix_mismatch',
 'LeanControls.DigitalHold.digital_invariant','LeanControls.DigitalHold.sampled_hold',
 'LeanControls.DigitalHold.DispatchWitness.two_cell_sampled_execution',
 'LeanControls.DigitalHold.DispatchWitness.not_classical_at_dispatch']))
run('statement-audit',[lean,fresh/'Statements.lean'])
for n in ['DigitalHold','DispatchWitness']:
    run('kernel-'+n,[checker,n,'-v'])
# Independent semantic and exact arithmetic checks composed from the frozen API.
(fresh/'CriticChecks.lean').write_text('''import DispatchWitness
open Set
open LeanControls.DigitalHold
namespace IndependentCritic
example : (103621708/1000000000:ℝ) + 98304/1000000*radius = 136350047/1250000000 := by
  norm_num [radius]
example : (2*radius - ((103621708/1000000000:ℝ) + 98304/1000000*radius)) = 2462453/1250000000 := by
  norm_num [radius]
example {H c t : ℝ} {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H c f r d stamp read) (b : Bool) (ht : t ∈ Icc 0 H) : ¬ t < stamp b t := by
  exact not_lt_of_ge (ex.causal b t ht).2.1
example {H : ℝ} (hH : 0 ≤ H) {q : Schedule} {stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hs : IsSchedule H q stamp read) (b : Bool) : stamp b 0=0 := by
  exact (first_command_fresh hH hs b).1
example : (0:ℝ)-1 ≤ 1/1000 ∧ ¬ (1:ℝ) ≤ 0 := by norm_num
example : ¬ ((103621708/1000000000:ℝ) + 98304/1000000*radius ≤ 2*radius-1/500) := by
  norm_num [radius]
example : |command 0 (![-1/1000,-1/100,-1/20]) - command 0 (![0,0,0])| = 93/1000 := by
  norm_num [command]
example : |command 0 (![-1/1000,-1/100,-1/20]) - command 0 (![0,0,0])| > 92/1000 := by
  norm_num [command]
example : ¬ DifferentiableAt ℝ (fun t => DispatchWitness.state t 2) DispatchWitness.switch :=
  DispatchWitness.not_classical_at_dispatch
example : ∀ t ∈ Icc 0 (1/1000:ℝ), ∀ i,
    |coordinates 0 (DispatchWitness.state t) i| ≤ radius := by
  exact (sampled_hold (by norm_num) DispatchWitness.two_cell_sampled_execution.1
    DispatchWitness.two_cell_sampled_execution.2).2.1
end IndependentCritic
''')
run('independent-semantic-checks',[lean,'--root='+str(fresh),'-o',fresh/'CriticChecks.olean',fresh/'CriticChecks.lean'])
run('kernel-CriticChecks',[checker,'CriticChecks','-v'])
# Reuse the builder's exact two mathematical mutants, but build fresh copies.
for n in ['reject-5ms-age','reject-smaller-cube']:
    shutil.copy2(BUILDER/'negative-controls'/(n+'.lean'),fresh/(n+'.lean'))
    run(n,[lean,'--root='+str(fresh),fresh/(n+'.lean')],negative=True)
(fresh/'RejectFalseSlack.lean').write_text('''import DigitalHold
open LeanControls.DigitalHold
example : (103621708/1000000000:ℝ) + 98304/1000000*radius ≤ 2*radius-1/500 := by
  norm_num [radius]
''')
run('reject-false-slack',[lean,fresh/'RejectFalseSlack.lean'],negative=True)
(fresh/'RejectSensorBudget.lean').write_text('''import DigitalHold
open LeanControls.DigitalHold
example : |command 0 (![-1/1000,-1/100,-1/20]) - command 0 (![0,0,0])| ≤ 92/1000 := by
  norm_num [command]
''')
run('reject-sensor-underbudget',[lean,fresh/'RejectSensorBudget.lean'],negative=True)
verify_frozen()
report['frozen_files_verified_after']=len(manifest['files'])
report['fresh_source_unchanged']=all(sha(fresh/(n+'.lean'))==h for n,h in report['source_sha256'].items())
report['replay_script_sha256']=sha(Path(__file__))
report['passed']=report['fresh_source_unchanged'] and all(x['passed'] for x in report['steps'])
save();print(json.dumps({'passed':report['passed'],'theorem_count':len(names),'steps':len(report['steps'])}),flush=True)
