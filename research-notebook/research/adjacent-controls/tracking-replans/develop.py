from pathlib import Path
import os, subprocess, shutil, sys
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[2];BASE=WORK/'lean-controls';BUILD=HERE/'.lake/check';BUILD.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args): return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=query('which','lean')
dep=':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':'))
env['LEAN_PATH']=str(BUILD)+':'+dep
sources=[HERE.parent/'variable-response/ComparisonEnvelope.lean',HERE.parent/'variable-response/sampled-handoff/RobustHold.lean',HERE.parent/'vla-smooth-replanning/SmoothReplan.lean',HERE/'TrackingReplan.lean']
if len(sys.argv)>1:sources.extend(HERE/(n+'.lean') for n in sys.argv[1:])
for src in sources:
    dst=BUILD/src.name;out=dst.with_suffix('.olean')
    if not dst.exists() or dst.read_bytes()!=src.read_bytes() or not out.exists():
        shutil.copy2(src,dst)
        print('Building',src.name,flush=True)
        subprocess.run([lean,'--root='+str(BUILD),'-o',str(out),str(dst)],cwd=BUILD,env=env,check=True)
