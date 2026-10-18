from pathlib import Path
import os,subprocess,shutil,json
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BASE=WORK/'lean-controls'
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def q(*a):return subprocess.check_output([lake,'env',*a],cwd=BASE,env=env,text=True).strip()
lean=q('which','lean')
dep=':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in q('printenv','LEAN_PATH').split(':'))
root=HERE/'build';env['LEAN_PATH']=str(root)+':'+dep
root.mkdir(exist_ok=True)
p=WORK/'research/adjacent-controls/variable-response/ComparisonEnvelope.lean'
if not (root/'ComparisonEnvelope.olean').exists():
 shutil.copy2(p,root/p.name)
 subprocess.run([lean,'--root='+str(root),'-o',str(root/'ComparisonEnvelope.olean'),str(root/p.name)],cwd=root,env=env,check=True)
shutil.copy2(HERE/'QuadraticSlowFilter.lean',root/'QuadraticSlowFilter.lean')
r=subprocess.run([lean,'--root='+str(root),'-o',str(root/'QuadraticSlowFilter.olean'),str(root/'QuadraticSlowFilter.lean')],cwd=root,env=env)
raise SystemExit(r.returncode)
