#!/usr/bin/env python3
"""Independent frozen handoff replay; all writes stay under critic/handoff/."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]; BASE=WORK/'lean-controls'; B=HERE.parent/'handoff-builder'
OUT=HERE/'handoff'; OUT.mkdir(exist_ok=True)
FRESH=OUT/'fresh';FRESH.mkdir(exist_ok=True)
assert not list(FRESH.iterdir()),'Use a new critic-owned replay directory'
LOG=OUT/'logs';LOG.mkdir(exist_ok=True)
EXPECTED='0ca3f54c0d77ff244866bb5a861c6d701749594d6d155c87ba9ab7338e23276e'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def frozen():
 assert sha(B/'artifact-sha256.json')==EXPECTED
 m=json.loads((B/'artifact-sha256.json').read_text())
 assert len(m['files'])==49
 for f,h in m['files'].items(): assert sha(B/f)==h,f
 return m
m=frozen();shutil.copy2(B/'artifact-sha256.json',OUT/'builder-manifest.json')
mods=['DigitalHold','DelayedHold','DelayedWitness','BrakingDelayedHold','BrakingDelayedWitness']
sources={n:B/('inputs/' if n=='DigitalHold' else '')/(n+'.lean') for n in mods}
for n,p in sources.items():
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text())
 shutil.copy2(p,FRESH/(n+'.lean'))
assert sha(FRESH/'DigitalHold.lean')=='aa91b649affc0906c79dd7a017b34d6f729d1c16f50117ab87daaa1ed2fadc03'
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=Path(query('which','lean'));checker=lean.with_name('leanchecker')
paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
paths=[p for p in paths if '.lake/packages/' in p];assert paths
env['LEAN_PATH']=str(FRESH)+':'+':'.join(paths);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
report={'passed':False,'scope':'Five complete local proof modules copied and rebuilt; only pinned package products reused. Independent axiom and separate kernel replay.',
 'builder_manifest_sha256':EXPECTED,'frozen_files_before':49,'source_sha256':{n:sha(p) for n,p in sources.items()},
 'toolchain':query('lean','--version'),'lean_sha256':sha(lean),'leanchecker_sha256':sha(checker),
 'lean_toolchain_sha256':sha(BASE/'lean-toolchain'),'lake_manifest_sha256':sha(BASE/'lake-manifest.json'),
 'package_revisions':json.loads((BASE/'lake-manifest.json').read_text())['packages'],'lean_path':env['LEAN_PATH'],'steps':[],'axioms':{}}
def save():(OUT/'replay-results.json').write_text(json.dumps(report,indent=2)+'\n')
def run(label,args,negative=False):
 start=time.monotonic();p=LOG/(label+'.log')
 with p.open('w') as out:r=subprocess.run(list(map(str,args)),cwd=FRESH,env=env,stdout=out,stderr=subprocess.STDOUT)
 raw=p.read_text();ok=r.returncode==0 if not negative else r.returncode!=0 and 'error:' in raw and ('unsolved goals' in raw or 'linarith failed' in raw) and 'unknown' not in raw.lower()
 report['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':r.returncode,'passed':ok,'expected':'mathematical rejection' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(p)})
 save();print(label,r.returncode,ok,flush=True);assert ok,label
names=[]
for n in mods:
 p=FRESH/(n+'.lean');raw=p.read_text();ns=re.search(r'^namespace (\S+)',raw,re.M).group(1)
 names += [ns+'.'+t for t in re.findall(r'^theorem (\w+)',raw,re.M)]
 run('build-'+n,[lean,'--root='+str(FRESH),'-o',FRESH/(n+'.olean'),p])
(FRESH/'Audit.lean').write_text('import DelayedWitness\nimport BrakingDelayedWitness\n'+''.join('#print axioms '+n+'\n' for n in names))
run('axiom-audit',[lean,FRESH/'Audit.lean'])
for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOG/'axiom-audit.log').read_text()):
 a={s.strip() for s in body.split(',') if s.strip()};assert a<={'propext','Classical.choice','Quot.sound'}
 report['axioms'][n]=sorted(a)
assert set(report['axioms'])==set(names);report['theorem_count']=len(names);save()
(FRESH/'Statements.lean').write_text('import DelayedWitness\nimport BrakingDelayedWitness\n'+''.join('#print '+n+'\n' for n in ['LeanControls.BrakingDelayedHold.Execution','LeanControls.BrakingDelayedHold.IsSchedule','LeanControls.BrakingDelayedHold.observation_admission','LeanControls.BrakingDelayedHold.delayed_sampled_hold','LeanControls.BrakingDelayedHold.no_first_hold_after_full_age','LeanControls.BrakingDelayedHold.Witness.positive_delay_witness']))
run('statement-audit',[lean,FRESH/'Statements.lean'])
for n in mods:run('kernel-'+n,[checker,n,'-v'])
# Recompile mathematical mutants, never the builder's compiled products.
for p in sorted((B/'negative-controls').glob('*.lean')):
 shutil.copy2(p,FRESH/p.name);run(p.stem,[lean,'--root='+str(FRESH),FRESH/p.name],negative=True)
(FRESH/'CriticHandoffChecks.lean').write_text('''import DelayedWitness
import BrakingDelayedWitness
open Set LeanControls.DigitalHold
namespace IndependentHandoffCritic
example : (2*radius-(111/1000:ℝ))=1/20000 := by norm_num [radius]
example : (2*radius-(11/100:ℝ))=21/20000 := by norm_num [radius]
example : (1/2000:ℝ)+(1/1000:ℝ)>1/1000 := by norm_num
example : LeanControls.BrakingDelayedHold.startupLimit < (1/1000:ℝ) := by
 norm_num [LeanControls.BrakingDelayedHold.startupLimit]
example : LeanControls.BrakingDelayedHold.actualCommand (1/2000) LeanControls.BrakingDelayedHold.center
 (fun _ _ => LeanControls.BrakingDelayedHold.exampleReading) false (1/2000) = -121/100 := by
 norm_num [LeanControls.BrakingDelayedHold.actualCommand]
example : LeanControls.BrakingDelayedHold.actualCommand (1/2000) LeanControls.BrakingDelayedHold.center
 (fun _ _ => LeanControls.BrakingDelayedHold.exampleReading) true (1/2000) = 23/100 := by
 norm_num [LeanControls.BrakingDelayedHold.actualCommand,LeanControls.BrakingDelayedHold.center,
  LeanControls.BrakingDelayedHold.exampleReading,command,clip]
example : LeanControls.BrakingDelayedHold.Witness.state LeanControls.BrakingDelayedHold.Witness.delay 2 <
 LeanControls.BrakingDelayedHold.exampleReading 2 :=
 LeanControls.BrakingDelayedHold.Witness.nonzero_delay_and_changed_state.2
example : LeanControls.DelayedHold.Witness.state LeanControls.DelayedHold.Witness.delay 2 >
 LeanControls.DelayedHold.exampleReading 2 := LeanControls.DelayedHold.Witness.nonzero_delay_and_changed_state.2
example {d : ℝ} (hd : |d|≤1/100) : (-121/100:ℝ)+d≤-6/5 :=
 (LeanControls.BrakingDelayedHold.pending_braking_compatibility hd).2
example : ¬ ((-1:ℝ)+1/100≤-6/5) := by norm_num
end IndependentHandoffCritic
''')
run('critic-semantic-checks',[lean,'--root='+str(FRESH),'-o',FRESH/'CriticHandoffChecks.olean',FRESH/'CriticHandoffChecks.lean'])
run('kernel-CriticHandoffChecks',[checker,'CriticHandoffChecks','-v'])
(FRESH/'RejectWidenedMargin.lean').write_text('import DigitalHold\nopen LeanControls.DigitalHold\nexample : (111/1000:ℝ)≤2*radius-1/10000 := by norm_num [radius]\n')
run('reject-widened-margin',[lean,FRESH/'RejectWidenedMargin.lean'],negative=True)
frozen();report['frozen_files_after']=49
report['source_unchanged']=all(sha(p)==report['source_sha256'][n] and sha(FRESH/(n+'.lean'))==report['source_sha256'][n] for n,p in sources.items())
bv=json.loads((B/'verification.json').read_text())
report['toolchain_pins_match_builder']=all(report[k]==bv[k] for k in ['toolchain','lean_sha256','leanchecker_sha256','lean_toolchain_sha256','lake_manifest_sha256','package_revisions'])
report['script_sha256']=sha(Path(__file__));report['passed']=report['source_unchanged'] and report['toolchain_pins_match_builder'] and all(s['passed'] for s in report['steps'])
save();print(json.dumps({'passed':report['passed'],'theorems':len(names),'steps':len(report['steps'])}),flush=True)
