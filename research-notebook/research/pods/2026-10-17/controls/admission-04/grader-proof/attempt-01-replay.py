#!/usr/bin/env python3
"""Independent frozen-source replay. No Git commands or builder writes."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, time

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[5]
BUILDER = HERE.parent/'builder'
BASE = WORK/'lean-controls'
OUT = HERE/'fresh'
LOGS = HERE/'logs'
OUT.mkdir(exist_ok=False)
LOGS.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((BUILDER/'artifact-sha256.json').read_text())
before = {n:sha(BUILDER/n) for n in manifest}
assert before == manifest
source = BUILDER/'CausalAdmission.lean'
assert sha(source) == '3abee2a4c0080f72e33676c3fd25fdd206db9fa70dcf4cf1fccc56b99cc1501a'
shutil.copyfile(source,OUT/source.name)
shutil.copyfile(BUILDER/'verify.py',HERE/'builder-verify.py')
shutil.copyfile(BUILDER/'MutationWitness.lean',OUT/'BuilderMutationWitness.lean')
assert sha(OUT/source.name)==sha(source)
env=os.environ.copy()
env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args):
    return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=Path(query('which','lean'))
checker=lean.with_name('leanchecker')
deps=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p
      for p in query('printenv','LEAN_PATH').split(':')]
env['LEAN_PATH']=str(OUT)+':'+':'.join(deps)
env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
lake_manifest=json.loads((BASE/'lake-manifest.json').read_text())
expected_revision=next(p['rev'] for p in lake_manifest['packages'] if p['name']=='mathlib')
gitdir=BASE/'.lake/packages/mathlib/.git'
head=(gitdir/'HEAD').read_text().strip()
if head.startswith('ref: '):
    ref=head[5:]
    if (gitdir/ref).exists(): head=(gitdir/ref).read_text().strip()
    else:
        head=next(line.split()[0] for line in (gitdir/'packed-refs').read_text().splitlines()
                  if not line.startswith(('#','^')) and line.split()[1]==ref)
assert head==expected_revision=='56a005855ea17e0b0958f73ec801ae140b0a1679'
text=source.read_text()
stripped=re.sub(r'/-.*?-/|--[^\n]*','',text,flags=re.S)
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',stripped)
names=['CausalAdmission.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
assert len(names)==len(set(names))==18
report={'passed':False,'source_sha256':sha(source),'builder_hashes_before':before,
    'toolchain':query('lean','--version'),'toolchain_pin':(BASE/'lean-toolchain').read_text().strip(),
    'mathlib_revision_from_files':head,'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),
    'lean_path':str(lean),'leanchecker_path':str(checker),'dependency_paths':deps,
    'scope':'New independent replay script. Fresh target olean. Pinned dependency caches reused. No Git commands.',
    'declarations':names,'steps':[]}
assert report['toolchain_pin']=='leanprover/lean4:v4.35.0'
assert report['lake_manifest_sha256']=='6525e7195148f78782a5aeeee8f1a8a90eebc4ecd4e9c3cdc215b29ddd3fbcb0'
def save(): (HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args,negative=False):
    start=time.monotonic()
    proc=subprocess.run(list(map(str,args)),cwd=OUT,env=env,text=True,stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,timeout=600)
    log=LOGS/(label+'.log'); log.write_text(proc.stdout)
    ok=(proc.returncode!=0) if negative else (proc.returncode==0)
    report['steps'].append({'label':label,'exit_code':proc.returncode,'passed':ok,
        'seconds':time.monotonic()-start,'log_sha256':sha(log)})
    save(); print(label,proc.returncode,flush=True); assert ok,label
    return proc.stdout
run('fresh-build',[lean,'--root='+str(OUT),'-o',OUT/'CausalAdmission.olean',OUT/source.name])
audit='import CausalAdmission\nset_option pp.universes true\n'
audit+='\n'.join('#check '+n for n in names)+'\n'
audit+='\n'.join('#print axioms '+n for n in names)+'\n'
audit+='#print CausalAdmission.IsAdmissible\n#print CausalAdmission.deadline\n'
(OUT/'Audit.lean').write_text(audit)
audit_output=run('statements-and-axioms',[lean,OUT/'Audit.lean'])
axioms={name:sorted(x.strip() for x in raw.split(',') if x.strip())
    for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",audit_output)}
assert set(axioms)==set(names)
assert all(set(xs)<={'propext','Classical.choice','Quot.sound'} for xs in axioms.values())
report['axioms']=axioms
run('independent-kernel',[checker,'CausalAdmission','-v'])
old='    deadline a0 J S ≤ T := by'
assert text.count(old)==1
(OUT/'FalseDeadline.lean').write_text(text.replace(old,'    deadline a0 J S + J / S ≤ T := by'))
bad=run('false-stronger-deadline',[lean,OUT/'FalseDeadline.lean'],negative=True)
assert 'linarith failed' in bad and 'error: unknown' not in bad
run('builder-witness-recompiled',[lean,OUT/'BuilderMutationWitness.lean'])
witness='''import CausalAdmission
open CausalAdmission
theorem falseStrongerDeadline : ¬ (∀ a j s : ℝ → ℝ,
    IsAdmissible (5/2) 10 400 (3/10) a j s → a (3/10) ≤ 0 →
    deadline (5/2) 10 400 + 10/400 ≤ (3/10 : ℝ)) := by
  intro h
  have ha : IsAdmissible (5/2) 10 400 (3/10)
      (leastAccel (5/2) 10 400) (leastJerk 10 400) (leastSnap 10 400) :=
    least_isAdmissible _ _ (by norm_num) (by norm_num)
  have hz : leastAccel (5/2) 10 400 (3/10) = 0 := by
    rw [← exact_earliest_deadline]
    exact least_reaches_zero (by norm_num) (by norm_num) (by norm_num)
  have hb := h _ _ _ ha hz.le
  norm_num [deadline, rampTime] at hb
#print axioms falseStrongerDeadline
'''
(OUT/'IndependentWitness.lean').write_text(witness)
run('independent-counterexample',[lean,'--root='+str(OUT),'-o',OUT/'IndependentWitness.olean',OUT/'IndependentWitness.lean'])
run('counterexample-kernel',[checker,'IndependentWitness','-v'])
after={n:sha(BUILDER/n) for n in manifest}
assert before==after
report['builder_hashes_after']=after
report['builder_sources_stable']=True
report['copied_source_stable']=sha(OUT/source.name)==sha(source)
report['negative_control_reason']='Main theorem arithmetic cannot prove the false extra J/S. A separate fresh theorem negates the universal claim using the fully admissible attainer at T=3/10 < 13/40.'
report['passed']=all(x['passed'] for x in report['steps'])
save(); print(json.dumps({'passed':report['passed'],'declarations':len(names),'source_stable':True}))
