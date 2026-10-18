from pathlib import Path
import os,re,shutil,subprocess,sys
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BASE=WORK/'lean-controls'
PRIOR=WORK/'research/pods/2026-10-17/robot-motion/certificate-03/builder'
EXTRA={
'ComparisonEnvelope':WORK/'research/adjacent-controls/variable-response/ComparisonEnvelope.lean',
'RobustHold':WORK/'research/adjacent-controls/variable-response/sampled-handoff/RobustHold.lean',
'SmoothReplan':WORK/'research/adjacent-controls/vla-smooth-replanning/SmoothReplan.lean',
'TrackingReplan':WORK/'research/adjacent-controls/tracking-replans/TrackingReplan.lean',
'ScaledTracking':WORK/'research/adjacent-controls/tracking-replans/ScaledTracking.lean'}
EXTRA.update({m:PRIOR/(m+'.lean') for m in ['Primitive','Kernel','Knots','RationalGuard','Reference','Admission','Composition','Fixtures']})
GATE1=HERE.parent/'builder-01'
EXTRA.update({m:GATE1/(m+'.lean') for m in ['AccelerationGuard','AccelerationFixtures','ReversalProposal','TimedAdmission']})
EXTRA['PhysicalArrival']=HERE/'PhysicalArrival.lean'
def source_closure(target):
    result={}
    def visit(m):
        if m in result:return
        p=EXTRA.get(m,BASE/(m.replace('.','/')+'.lean'))
        if not p.exists():return
        for dep in re.findall(r'^(?:public )?import (\S+)',p.read_text(),re.M):visit(dep)
        result[m]=p
    visit(target)
    return result
def environment():
    env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
    lake=str(WORK/'.tools/elan/bin/lake')
    def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
    lean=query('which','lean')
    deps=':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':'))
    return env,lean,deps
def main():
    name=sys.argv[1];env,lean,deps=environment();root=HERE/'.cache/dev';root.mkdir(parents=True,exist_ok=True)
    env['LEAN_PATH']=':'.join([str(root),str(PRIOR/'build'),deps])
    for m,p in source_closure(name).items():
        dst=root/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
        if dst.exists() and dst.read_bytes()==p.read_bytes() and dst.with_suffix('.olean').exists():continue
        shutil.copyfile(p,dst)
        proc=subprocess.run([lean,'--root='+str(root),'-o',str(dst.with_suffix('.olean')),str(dst)],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (HERE/(m.replace('.','_')+'-development.log')).write_text(proc.stdout);print(m,proc.stdout,flush=True)
        if proc.returncode:sys.exit(proc.returncode)
if __name__=='__main__':main()
