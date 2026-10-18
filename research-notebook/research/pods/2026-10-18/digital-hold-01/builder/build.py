from pathlib import Path
import os, subprocess, shutil, json, sys, time, hashlib
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BASE=WORK/'lean-controls'
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=query('which','lean')
dep=':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':'))
root=HERE/'build';root.mkdir(exist_ok=True)
env['LEAN_PATH']=str(root)+':'+dep
env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
for m,p in [('DigitalHold',HERE/'DigitalHold.lean'),('DispatchWitness',HERE/'DispatchWitness.lean')]:
    dst=root/p.name
    if m!='DigitalHold' and dst.exists() and dst.read_bytes()==p.read_bytes() and (root/(m+'.olean')).exists():continue
    shutil.copy2(p,dst)
    start=time.monotonic()
    out=subprocess.run([lean,'--root='+str(root),'-o',str(root/(m+'.olean')),str(dst)],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (HERE/'verification-logs'/('development-'+m+'.log')).write_text(out.stdout)
    print(m,out.returncode,round(time.monotonic()-start,2));print(out.stdout,flush=True)
    if out.returncode:sys.exit(out.returncode)
