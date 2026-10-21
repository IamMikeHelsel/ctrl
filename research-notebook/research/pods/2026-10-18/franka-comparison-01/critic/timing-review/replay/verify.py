#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,json,hashlib,re,shutil,time
P=Path(__file__).resolve().parent; W=Path('/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes'); B=W/'lean-controls'
F=P/'fresh-replay';L=P/'verification-logs';OLD=W/'research/pods/2026-10-18/method-transfer-01/controls'
MODS=['DigitalHold','WeightedEntry','ClearancePolicy','AgeBudget','TimingClock','TimingAdmission','TimingEntry']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 F.mkdir(exist_ok=True);L.mkdir(exist_ok=True);assert not list(F.iterdir())
 sources={m:(P/'inputs' if i<3 else P)/(m+'.lean') for i,m in enumerate(MODS)}
 original={m:sha(p) for m,p in sources.items()}
 old_packets=['milestone-01','finite-entry-02','adaptive-admission-03','delayed-entry-04','clearance-policy-05','detector-bridge-06','constructive-hold-07','constructed-handoff-08']
 old_manifests={n:sha(OLD/n/'frozen-manifest.json') for n in old_packets}
 def preserve():
  for n,h in old_manifests.items():
   p=OLD/n/'frozen-manifest.json';assert sha(p)==h
   assert all(sha(p.parent/f)==v for f,v in json.loads(p.read_text())['files'].items())
  for r in json.loads((P/'INPUTS.json').read_text()):assert sha(W/r['source'])==sha(P/r['copy'])==r['sha256']
  for r in json.loads((P/'PINS.json').read_text()):assert sha(W/r['path'])==r['sha256']
 preserve()
 graph={m:re.findall(r'^(?:public |private )?import (\S+)',p.read_text(),re.M) for m,p in sources.items()}
 assert all(n.startswith('Mathlib.') or n in sources for deps in graph.values() for n in deps)
 for m,p in sources.items():
  assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text()),m
  shutil.copy2(p,F/(m+'.lean'))
 env=os.environ.copy();env['ELAN_HOME']=str(W/'.tools/elan');lake=W/'.tools/elan/bin/lake'
 def q(*args):return subprocess.check_output([str(lake),'env',*args],cwd=B,env=env,text=True).strip()
 lean=Path(q('which','lean'));checker=lean.with_name('leanchecker')
 paths=[str((B/x).resolve()) if not Path(x).is_absolute() else x for x in q('printenv','LEAN_PATH').split(':')];paths=[x for x in paths if '.lake/packages/' in x]
 assert paths and str(B/'.lake/build/lib/lean') not in paths
 env['LEAN_PATH']=str(F)+':'+':'.join(paths);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 r={'passed':False,'scope':'Seven local research modules rebuilt from copied sources. They import only these modules and pinned Mathlib package artifacts; no local LeanControls cache or C8 constructor is imported.',
 'source_sha256':original,'import_graph':graph,'build_order':MODS,'prior_frozen_manifests':old_manifests,
 'toolchain':q('lean','--version'),'lean_sha256':sha(lean),'leanchecker_sha256':sha(checker),'lean_toolchain_sha256':sha(B/'lean-toolchain'),'lake_manifest_sha256':sha(B/'lake-manifest.json'),
 'package_revisions':json.loads((B/'lake-manifest.json').read_text())['packages'],'lean_path':env['LEAN_PATH'],'verifier_sha256':sha(Path(__file__)),'steps':[],'axioms':{}}
 prior=json.loads((OLD/'milestone-01/verification.json').read_text())
 for k in ['toolchain','lean_sha256','leanchecker_sha256','lean_toolchain_sha256','lake_manifest_sha256']:assert r[k]==prior[k]
 def save():(P/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
 def run(label,args,negative=False):
  start=time.monotonic();p=L/(label+'.log')
  with p.open('w') as f:cp=subprocess.run(list(map(str,args)),cwd=F,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180)
  raw=p.read_text()
  passed=cp.returncode==0 if not negative else cp.returncode!=0 and 'error:' in raw and any(s in raw for s in ['unsolved goals','linarith failed','Type mismatch','Application type mismatch']) and not any(s in raw.lower() for s in ['unknown identifier','unknown module','no such file','ambiguous'])
  r['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':cp.returncode,'passed':passed,'expected':'semantic rejection' if negative else 'success','seconds':round(time.monotonic()-start,4),'log_sha256':sha(p)})
  save();print(label,cp.returncode,passed,flush=True);assert passed,label
 for m in MODS:run('build-'+m,[lean,'--root='+str(F),'-o',F/(m+'.olean'),F/(m+'.lean')])
 names=[];inventory={}
 for m,p in sources.items():
  raw=p.read_text();ns=re.search(r'^namespace (\S+)',raw,re.M).group(1)
  pubs=re.findall(r'^(?:protected )?(?:theorem|lemma) (\w+)',raw,re.M)
  privs=re.findall(r'^private (?:theorem|lemma) (\w+)',raw,re.M)
  inventory[m]={'public':pubs,'private':privs};names.extend(ns+'.'+n for n in pubs)
 assert len(names)==len(set(names))
 r['declaration_inventory']=inventory
 (F/'Audit.lean').write_text('import TimingEntry\n'+''.join('#print axioms '+n+'\n' for n in names))
 run('axiom-audit',[lean,F/'Audit.lean'])
 for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(L/'axiom-audit.log').read_text()):
  a={s.strip() for s in body.split(',') if s.strip()};assert a<={'propext','Classical.choice','Quot.sound'},(n,a);r['axioms'][n]=sorted(a)
 assert set(r['axioms'])==set(names);save()
 for m in MODS:run('kernel-'+m,[checker,m,'-v'])
 N=P/'negative-controls';N.mkdir()
 mutations=[('DroppedPendingOverlap','AgeBudget','|g t-g s|≤P*d+L*(a-d) := by','|g t-g s|≤L*a := by'),('RenewedStamp','TimingClock','ℝ := sample (index b t)','ℝ := sample (index b t)+delay')]
 for label,mod,old,new in mutations:
  raw=sources[mod].read_text();assert old in raw;p=N/(label+'.lean');p.write_text(raw.replace(old,new,1));run('reject-'+label,[lean,'--root='+str(N),p],True)
 claims={
 'FalseOldCubeBudget':'''import TimingEntry
open LeanControls.TimingBudget LeanControls.DigitalHold
example : splitResidual age delay radius≤2*radius := by
 norm_num [splitResidual,digitalSlope,firstResidual,coarseSlope,noise,age,delay,radius]
''',
 'FalseNaiveFace':'''import TimingEntry
open LeanControls.DigitalHold LeanControls.WeightedEntry
example : transformedRHS 12 (115/1000) ![-(51/50)*target,(101/100)*target,target] 2≤0 := by
 norm_num [transformedRHS,target]
''',
 'FalseOldDrift':'''import TimingEntry
open LeanControls.DigitalHold LeanControls.WeightedEntry
example : transformedRHS 12 LeanControls.TimingBudget.residual ![-(51/50)*target,(101/100)*target,target] 2≤-drift := by
 norm_num [transformedRHS,target,LeanControls.TimingBudget.residual,drift]
''',
 'FalseOneMillisecondAge':'''import TimingEntry
open LeanControls.TimingClock
example : dispatch 1-stamp false (dispatch 1)≤1/1000 := by
 rw [second_dispatch_sides.2.2.1]
 norm_num
''',
 'FalseFreshIncomingStamp':'''import TimingEntry
open LeanControls.TimingClock
example : stamp false (dispatch 1)=sample 1 := by
 rw [second_dispatch_sides.1]
 norm_num [sample]
''',
 'FalseOldDerivedCommandBound':'''import TimingEntry
open LeanControls.TimingBudget
example : 24*supportRadius+noise≤3589/2500 := by
 norm_num [supportRadius,noise]
'''}
 for label,body in claims.items():
  p=N/(label+'.lean');p.write_text(body);run('reject-'+label,[lean,p],True)
 preserve();r['prior_frozen_preserved']=True;r['source_unchanged']=all(sha(p)==original[m] and sha(F/(m+'.lean'))==original[m] for m,p in sources.items())
 r['passed']=r['source_unchanged'] and all(s['passed'] for s in r['steps']);save();print(json.dumps({'passed':r['passed'],'steps':len(r['steps']),'closures':len(r['axioms'])}),flush=True)
if __name__=='__main__':main()
