#!/usr/bin/env python3
"""Independent recovery replay. Writes only critic/grip; no cached local oleans."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent; WORK=HERE.parents[4];BASE=WORK/'lean-controls';B=HERE.parent/'grip-builder'
OUT=HERE/'grip';OUT.mkdir(exist_ok=True);FRESH=OUT/'fresh';FRESH.mkdir(exist_ok=True)
assert not list(FRESH.iterdir()),'Use fresh critic-owned scratch, never overwrite frozen replay'
LOG=OUT/'logs';LOG.mkdir(exist_ok=True)
EXPECTED='c51f6effdb28ed5dcd31b0dd9079e9258f48d697ae4c59643f7ffa67060f7a90'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def frozen():
 assert sha(B/'frozen-manifest.json')==EXPECTED
 d=json.loads((B/'frozen-manifest.json').read_text());assert len(d['files'])==49
 for p,h in d['files'].items():assert sha(B/p)==h,p
 return d
fm=frozen();shutil.copy2(B/'frozen-manifest.json',OUT/'builder-manifest.json')
bv=json.loads((B/'verification.json').read_text())
mods=['ComparisonEnvelope','FirstStop','StoppingCertificate','ActualStop','Recovery','RecoveryWitness']
sources={n:(B if n.startswith('Recovery') else B/'inputs')/(n+'.lean') for n in mods}
core={};order=[]
def visit(n):
 if n in core:return
 p=BASE/Path(n.replace('.','/')+'.lean');core[n]=p
 for line in re.findall(r'^(?:public |private )?import (.+)$',p.read_text(),re.M):
  for imp in line.split():
   if imp.startswith('LeanControls.'):visit(imp)
 order.append(n)
visit('LeanControls.UncertainLag')
for n,p in core.items():
 assert sha(p)==bv['cached_core_source_sha256'][str(p.relative_to(WORK))],n
for n,p in {**core,**sources}.items():
 dst=FRESH/Path(n.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
for p in sources.values():assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text())
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan');lake=str(WORK/'.tools/elan/bin/lake')
def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=Path(query('which','lean'));checker=lean.with_name('leanchecker')
paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
paths=[p for p in paths if '.lake/packages/' in p];assert paths
assert not any(p==str(BASE/'.lake/build/lib/lean') for p in paths)
env['LEAN_PATH']=str(FRESH)+':'+':'.join(paths);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
report={'passed':False,'scope':'All 31 local LeanControls dependency modules and six research modules copied byte-for-byte and rebuilt. Only pinned package products reused. Independent axiom audit and separate kernel replay.',
 'builder_manifest_sha256':EXPECTED,'frozen_files_before':49,'source_sha256':{n:sha(p) for n,p in sources.items()},
 'core_source_sha256':{n:sha(p) for n,p in core.items()},'core_build_order':order,
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
for n in order+mods:
 p=FRESH/Path(n.replace('.','/')+'.lean')
 run('build-'+n,[lean,'--root='+str(FRESH),'-o',p.with_suffix('.olean'),p])
names=[]
for n,p in sources.items():
 raw=p.read_text();ns=re.search(r'^namespace (\S+)',raw,re.M).group(1)
 names += [ns+'.'+t for t in re.findall(r'^theorem (\w+)',raw,re.M)]
names+=['LeanControls.UncertainLag.exact_initial','LeanControls.UncertainLag.exact_ode']
(FRESH/'Audit.lean').write_text('import RecoveryWitness\n'+''.join('#print axioms '+n+'\n' for n in names))
run('axiom-audit',[lean,FRESH/'Audit.lean'])
for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(LOG/'axiom-audit.log').read_text()):
 a={s.strip() for s in body.split(',') if s.strip()};assert a<={'propext','Classical.choice','Quot.sound'},(n,a)
 report['axioms'][n]=sorted(a)
assert set(report['axioms'])==set(names);report['theorem_count']=len(names);save()
(FRESH/'Statements.lean').write_text('import RecoveryWitness\n'+''.join('#print '+n+'\n' for n in ['LeanControls.VariableResponse.IsTrajectory','LeanControls.Recovery.recovered_upper_flow','LeanControls.Recovery.restored_braking_first_zero','LeanControls.Recovery.no_recovery_counterexample','LeanControls.Recovery.Witness.state','LeanControls.Recovery.Witness.coast_then_brake_trajectory','LeanControls.Recovery.Witness.coast_then_brake_first_zero']))
run('statement-audit',[lean,FRESH/'Statements.lean'])
for n in order+mods:run('kernel-'+n,[checker,n,'-v'])
for p in sorted((B/'negative-controls').glob('*.lean')):
 shutil.copy2(p,FRESH/p.name);run('reject-'+p.stem,[lean,'--root='+str(FRESH),FRESH/p.name],negative=True)
(FRESH/'CriticRecoveryChecks.lean').write_text('''import RecoveryWitness
open Set LeanControls.Recovery
namespace IndependentRecoveryCritic
example : travelBudget (1/100) 0 0 1 8 = (729/80000:ℝ) := by
 norm_num [travelBudget,velocityBudget]
example : travelBudget (1/100) 0 0 1 8 < travelBudget (1/100) 0 0 2 8 := by
 norm_num [travelBudget,velocityBudget]
example : travelBudget 0 0 0 1 8 = (1/128:ℝ) := by
 norm_num [travelBudget,velocityBudget]
example : Witness.state 1 = ![(1:ℝ),1,0] := by norm_num [Witness.state,coast]
example {t : ℝ} (ht : t ≤ 1) : Witness.state t 1 = 1 ∧ Witness.state t 2 = 0 := by
 simp [Witness.state,ht,coast]
example : Witness.state 3 1 < 0 := by
 norm_num [Witness.state,LeanControls.UncertainLag.heldSolution]
 positivity
example : Witness.state 3 1 = -Real.exp (-2) := by
 norm_num [Witness.state,LeanControls.UncertainLag.heldSolution]
 ring
example : ¬ (∀ t : ℝ, 0 ≤ Witness.state t 1) := by
 intro h
 have hn : Witness.state 3 1 < 0 := by
  norm_num [Witness.state,LeanControls.UncertainLag.heldSolution]
  positivity
 linarith [h 3]
end IndependentRecoveryCritic
''')
run('critic-semantic-checks',[lean,'--root='+str(FRESH),'-o',FRESH/'CriticRecoveryChecks.olean',FRESH/'CriticRecoveryChecks.lean'])
run('kernel-CriticRecoveryChecks',[checker,'CriticRecoveryChecks','-v'])
(FRESH/'RejectMonotoneBrakingBudget.lean').write_text('import Recovery\nopen LeanControls.Recovery\nexample : travelBudget (1/100) 0 0 2 8 ≤ travelBudget (1/100) 0 0 1 8 := by\n norm_num [travelBudget,velocityBudget]\n')
run('reject-monotone-braking-budget',[lean,FRESH/'RejectMonotoneBrakingBudget.lean'],negative=True)
(FRESH/'RejectWitnessNonnegativeVelocity.lean').write_text('import RecoveryWitness\nopen LeanControls.Recovery\nexample : 0 ≤ Witness.state 3 1 := by\n norm_num [Witness.state,LeanControls.UncertainLag.heldSolution]\n have h := Real.exp_pos (-2:ℝ)\n linarith\n')
run('reject-witness-nonnegative-velocity',[lean,FRESH/'RejectWitnessNonnegativeVelocity.lean'],negative=True)
frozen();report['frozen_files_after']=49
report['source_unchanged']=all(sha(p)==report['source_sha256'][n] and sha(FRESH/(n+'.lean'))==sha(p) for n,p in sources.items())
report['core_source_unchanged']=all(sha(p)==report['core_source_sha256'][n] and sha(FRESH/Path(n.replace('.','/')+'.lean'))==sha(p) for n,p in core.items())
report['toolchain_pins_match_builder']=all(report[k]==bv[k] for k in ['toolchain','lean_sha256','leanchecker_sha256','lean_toolchain_sha256','lake_manifest_sha256'])
report['script_sha256']=sha(Path(__file__));report['passed']=report['source_unchanged'] and report['core_source_unchanged'] and report['toolchain_pins_match_builder'] and all(s['passed'] for s in report['steps'])
save();print(json.dumps({'passed':report['passed'],'theorems':len(names),'steps':len(report['steps'])}),flush=True)
