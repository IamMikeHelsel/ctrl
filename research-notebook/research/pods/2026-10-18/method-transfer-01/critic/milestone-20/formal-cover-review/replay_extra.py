#!/usr/bin/env python3
"""Add one safety-premise control using this review's successful fresh closure."""
from pathlib import Path
import sys,json,os,shutil,subprocess,hashlib,datetime,time,re
D=Path(__file__).resolve().parent
vpath=Path(sys.argv[1]).resolve();v=json.loads(vpath.read_text());assert v['passed']
work=vpath.parent;out=D/'extra-evidence';out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
names=['ReviewControls.lean','FalseUnguardedReciprocal.lean','FalseSquareBoundRepaired.lean']
for name in names:shutil.copyfile(D/name,out/name)
bins=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
paths=[str(out),*v['lean_path'].split(os.pathsep)]
assert str(work) in paths
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(paths)
r={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'main_verification':str(vpath.relative_to(D)),'main_verification_sha256':sha(vpath),'source_hashes':{n:sha(out/n) for n in names},'lean_path':env['LEAN_PATH'],'runs':[],'passed':False}
def save(): (out/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
def run(label,cmd):
 start=time.monotonic();p=subprocess.run(cmd,cwd=out,env=env,capture_output=True,text=True,timeout=180);log=p.stdout+p.stderr;(out/(label+'.log')).write_text(log)
 r['runs'].append({'label':label,'command':cmd,'exit':p.returncode,'seconds':time.monotonic()-start,'log':label+'.log'});save();print(label,p.returncode,flush=True);return p.returncode,log
code,log=run('compile-ReviewControls',[str(bins/'lean'),'-o','ReviewControls.olean','ReviewControls.lean']);assert code==0,log
axioms={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)}
for n in re.findall(r"'([^']+)' does not depend on any axioms",log):axioms[n]=[]
assert set(axioms)=={'E10.Review.reciprocal_guard_essential'}
assert set(axioms['E10.Review.reciprocal_guard_essential'])<={'propext','Classical.choice','Quot.sound'}
r['axioms']=axioms;save()
code,log=run('kernel-ReviewControls',[str(bins/'leanchecker'),'ReviewControls','-v']);assert code==0,log
for name in ['FalseSquareBoundRepaired','FalseUnguardedReciprocal']:
 code,log=run('reject-'+name,[str(bins/'lean'),name+'.lean'])
 assert code!=0 and 'unsolved goals' in log
 assert not re.search(r'Unknown identifier|unknown constant|unknown module|unexpected token|failed to synthesize|Type mismatch|Ambiguous term|\bsorry\b',log)
r['negative_goal_read']='The unguarded inverse interval (1,-1) cannot contain 2 at c=1/2 in [-1,1]. The source reduces the false membership to an unsolved mathematical goal.'
r['build_artifact_hashes']={p.name:sha(p) for p in out.iterdir() if p.is_file() and any(s in p.name for s in ['.olean','.ilean','.ir'])}
r['passed']=True;r['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
print(json.dumps({'passed':True,'steps':len(r['runs']),'axiom_closures':len(axioms),'kernels':1,'negative_controls':2}))
