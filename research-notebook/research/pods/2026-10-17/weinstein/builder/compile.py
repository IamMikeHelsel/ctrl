from pathlib import Path
import os, subprocess, sys
B=Path(__file__).resolve().parent
R=B.parents[4]
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan')
lake=str(R/'.tools/elan/bin/lake')
base=R/'lean-controls'
lean=subprocess.check_output([lake,'env','which','lean'],cwd=base,env=env,text=True).strip()
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=base,env=env,text=True).strip().split(':')
env['LEAN_PATH']=':'.join([str(B/'cache')]+[str((base/p).resolve()) for p in paths])
(B/'cache').mkdir(exist_ok=True)
(B/'logs').mkdir(exist_ok=True)
f=sys.argv[1] if len(sys.argv)>1 else 'HodgeBridge'
source=B/f'{f}.lean'
if not source.exists(): source=R/'research/weinstein-lean/operator-audit'/f'{f}.lean'
p=subprocess.run([lean,'--root='+str(source.parent),'-o',str(B/'cache'/f'{f}.olean'),str(source)],env=env,cwd=B,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(B/'logs'/f'last-{f}.log').write_text(p.stdout)
print(p.stdout);sys.exit(p.returncode)
