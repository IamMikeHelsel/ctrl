from pathlib import Path
import os, subprocess, sys
B=Path(__file__).resolve().parent
R=B.parents[5]
BASE=R/'lean-controls'
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan')
lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=BASE,env=env,text=True).strip().split(':')
env['LEAN_PATH']=str(B/'cache')+':'+':'.join(str((BASE/p).resolve()) for p in paths)
env['PATH']=str(Path(lean).parent)+':'+env['PATH']
for mod in sys.argv[1:]:
    own=B/(mod+'.lean')
    src=own if own.exists() else B.parent.parent/'clifford-contraction-03/builder'/(mod+'.lean')
    print('Building',mod,flush=True)
    p=subprocess.run([lean,'--root='+str(src.parent),'-o',str(B/'cache'/(mod+'.olean')),str(src)],cwd=BASE,env=env)
    if p.returncode:sys.exit(p.returncode)
