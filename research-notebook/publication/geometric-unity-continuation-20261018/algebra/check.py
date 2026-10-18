from pathlib import Path
import os,subprocess
B=Path(__file__).resolve().parent
R=Path('/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes')
L=R/'lean-controls'; old=R/'research/overnight/2026-10-18/geometric-unity/builder-05'
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');lake=str(R/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=L,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=L,env=env,text=True).strip().split(':')
env['LEAN_PATH']=':'.join([str(B),str(B.parent/'research-audit'),str(B.parent/'spin/cache'),str(old/'cache/fresh-01')]+[str((L/p).resolve()) for p in paths])
import sys
m=sys.argv[1] if len(sys.argv)>1 else 'SkewLie'
p=subprocess.run([lean,'-o',str(B/(m+'.olean')),str(B/(m+'.lean'))],cwd=B,env=env,text=True,capture_output=True)
print(p.stdout+p.stderr);raise SystemExit(p.returncode)
