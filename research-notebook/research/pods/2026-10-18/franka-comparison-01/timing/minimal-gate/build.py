from pathlib import Path
import os,subprocess,json,shutil
P=Path(__file__).resolve().parent; W=P.parents[4]; B=W/'lean-controls'; C=P/'build'; C.mkdir(exist_ok=True)
env=os.environ.copy();env['ELAN_HOME']=str(W/'.tools/elan');lake=W/'.tools/elan/bin/lake'
def q(*args):return subprocess.check_output([str(lake),'env',*args],cwd=B,env=env,text=True).strip()
lean=q('which','lean');paths=[str((B/x).resolve()) if not Path(x).is_absolute() else x for x in q('printenv','LEAN_PATH').split(':')];paths=[x for x in paths if '.lake/packages/' in x]
env['LEAN_PATH']=str(C)+':'+':'.join(paths)
for m in ['DigitalHold','WeightedEntry','ClearancePolicy','AgeBudget','TimingClock']:
 s=(P/'inputs' if m in ['DigitalHold','WeightedEntry','ClearancePolicy'] else P)/(m+'.lean');t=C/(m+'.lean');
 if not t.exists() or t.read_bytes()!=s.read_bytes():shutil.copy2(s,t)
 if not t.with_suffix('.olean').exists() or t.stat().st_mtime>t.with_suffix('.olean').stat().st_mtime:
  r=subprocess.run([lean,'--root='+str(C),'-o',str(t.with_suffix('.olean')),str(t)],cwd=C,env=env)
  if r.returncode:raise SystemExit(r.returncode)
