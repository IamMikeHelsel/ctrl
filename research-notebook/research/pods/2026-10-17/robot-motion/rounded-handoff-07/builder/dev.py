from pathlib import Path
import os,re,shutil,subprocess
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[5]
BASE=WORK/'lean-controls'
EXTRA={
'ComparisonEnvelope':WORK/'research/adjacent-controls/variable-response/ComparisonEnvelope.lean',
'RobustHold':WORK/'research/adjacent-controls/variable-response/sampled-handoff/RobustHold.lean',
'SmoothReplan':WORK/'research/adjacent-controls/vla-smooth-replanning/SmoothReplan.lean',
'TrackingReplan':WORK/'research/adjacent-controls/tracking-replans/TrackingReplan.lean',
'ScaledTracking':WORK/'research/adjacent-controls/tracking-replans/ScaledTracking.lean'}
TARGETS=['RoundedHandoff','HandoffWitnesses']
EXTRA.update({m:HERE/(m+'.lean') for m in TARGETS})
def source_closure(target):
    sources={}
    def visit(m):
        if m in sources:return
        p=EXTRA.get(m,BASE/(m.replace('.','/')+'.lean'))
        if not p.exists():return
        for dependency in re.findall(r'^(?:public )?import (\S+)',p.read_text(),re.M):visit(dependency)
        sources[m]=p
    visit(target)
    return sources

def environment():
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=str(WORK/'.tools/elan/bin/lake')
    def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
    lean=query('which','lean')
    dep=':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':'))
    return env,lean,dep

def main():
    import sys
    target=sys.argv[1] if len(sys.argv)>1 else 'RoundedHandoff'
    env,lean,dep=environment();root=HERE/'build';root.mkdir(exist_ok=True)
    env['LEAN_PATH']=str(root)+':'+dep
    env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    rebuilt=set()
    for m,p in source_closure(target).items():
        dst=root/(m.replace('.','/')+'.lean');out=dst.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
        dependencies=set(re.findall(r'^(?:public )?import (\S+)',p.read_text(),re.M))
        if not (rebuilt & dependencies) and dst.exists() and out.exists() and dst.read_bytes()==p.read_bytes():continue
        rebuilt.add(m);shutil.copy2(p,dst)
        print('BUILD',m,flush=True)
        subprocess.run([lean,'--root='+str(root),'-o',str(out),str(dst)],cwd=root,env=env,check=True)
if __name__=='__main__':main()
