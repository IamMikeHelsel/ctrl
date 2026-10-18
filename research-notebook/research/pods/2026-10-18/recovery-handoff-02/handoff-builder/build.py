from pathlib import Path
import os,subprocess,shutil,sys,time
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[4];BASE=WORK/'lean-controls'
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan');lake=str(WORK/'.tools/elan/bin/lake')
def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=query('which','lean');paths=[str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':')]
root=HERE/'build';root.mkdir(exist_ok=True);env['LEAN_PATH']=str(root)+':'+':'.join(p for p in paths if '.lake/packages/' in p)
env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
mods=[('DigitalHold',HERE/'inputs/DigitalHold.lean'),('DelayedHold',HERE/'DelayedHold.lean')]
if (HERE/'DelayedWitness.lean').exists():mods.append(('DelayedWitness',HERE/'DelayedWitness.lean'))
for m in ['BrakingDelayedHold','BrakingDelayedWitness']:
    if (HERE/(m+'.lean')).exists():mods.append((m,HERE/(m+'.lean')))
for m,p in mods:
    dst=root/p.name
    if m=='DigitalHold' and dst.exists() and dst.read_bytes()==p.read_bytes() and (root/(m+'.olean')).exists():continue
    shutil.copy2(p,dst);started=time.monotonic()
    proc=subprocess.run([lean,'--root='+str(root),'-o',str(root/(m+'.olean')),str(dst)],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=HERE/'verification-logs'/('development-'+m+'.log');log.write_text(proc.stdout)
    if proc.returncode:
        tag=str(time.time_ns());shutil.copy2(dst,HERE/'attempts'/(tag+'-'+m+'.lean'));shutil.copy2(log,HERE/'attempts'/(tag+'-'+m+'.log'))
    print(m,proc.returncode,round(time.monotonic()-started,2));print(proc.stdout,flush=True)
    if proc.returncode:sys.exit(proc.returncode)
