from pathlib import Path
import os, subprocess, sys
B=Path(__file__).resolve().parent
R=Path('/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes')
BASE=R/'lean-controls'; env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan')
lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=BASE,env=env,text=True).strip().split(':')
env['LEAN_PATH']=str(B/'cache')+':'+str(R/'research/overnight/2026-10-18/geometric-unity/builder-05/cache/fresh-01')+':'+':'.join(str((BASE/p).resolve()) for p in paths if not p.startswith('.lake/build'))
for mod in sys.argv[1:]:
 p=subprocess.run([lean,'--root='+str(B),'-o',str(B/'cache'/(mod+'.olean')),str(B/(mod+'.lean'))],cwd=BASE,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (B/'logs'/('compile-'+mod+'.txt')).write_text(p.stdout);print(p.stdout)
 if p.returncode:sys.exit(p.returncode)
