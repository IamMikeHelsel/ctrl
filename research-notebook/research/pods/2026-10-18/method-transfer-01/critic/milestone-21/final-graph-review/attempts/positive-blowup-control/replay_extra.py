#!/usr/bin/env python3
"""Run only after the fresh main E11 replay passes. Never uses builder products."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,re,shutil,subprocess,tempfile

H=Path(__file__).resolve().parent
ROOT=next(p for p in H.parents if (p/'lean-controls').is_dir())
BIN=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
main_candidates=[]
for p in (H/'builder-copy/evidence').glob('fresh-source-*/verification.json'):
    d=json.loads(p.read_text())
    # Builder's archived run is retained but excluded from this review.
    if str(H) in d.get('lean_path','') and d.get('passed'):
        main_candidates.append((p,d))
assert len(main_candidates)==1, main_candidates
main_path,main=main_candidates[0];fresh=main_path.parent
out=Path(tempfile.mkdtemp(prefix='extra-',dir=H))
shutil.copyfile(H/'ReviewControls.lean',out/'ReviewControls.lean')
(out/'MissingPositiveBlowup.lean').write_text('''import ReviewControls
open Erdos128 Erdos128.FinalControls E11Critic
example : HasNormalizedInternalCutBoundQ (balancedBlowup cycle5 0) 0 ↔
    HasNormalizedInternalCutBoundQ cycle5 0 := by
  have h := positive_blowup_needed
  simp_all
''')
deps=sorted(p/'.lake/build/lib/lean' for p in (ROOT/'lean-controls/.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir())
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[out,fresh,*deps]));env['PATH']=str(BIN)+os.pathsep+env.get('PATH','')
result={'started_utc':datetime.now(timezone.utc).isoformat(),'main_verification':str(main_path.relative_to(H)),'main_verification_sha256':sha(main_path),'work':str(out.relative_to(H)),'lean_path':env['LEAN_PATH'],'runs':[],'passed':False}
def save():
    result['sources']={p.name:sha(p) for p in out.glob('*.lean')}
    (H/'extra-verification.json').write_text(json.dumps(result,indent=2)+'\n')
def run(name,args):
    p=subprocess.run(args,cwd=out,env=env,text=True,capture_output=True,timeout=90)
    log=p.stdout+p.stderr;(out/(name+'.log')).write_text(log)
    result['runs'].append({'label':name,'command':args,'exit':p.returncode,'log':str((out/(name+'.log')).relative_to(H))});save()
    return p.returncode,log
code,log=run('compile-ReviewControls',[str(BIN/'lean'),'-o','ReviewControls.olean','ReviewControls.lean'])
assert code==0,log
axioms={}
for line in log.splitlines():
    if ' depends on axioms: ' in line:
        name,rest=line.split(' depends on axioms: ',1);axioms[name[1:-1]]=[s.strip() for s in rest.strip('[]').split(',') if s.strip()]
    elif ' does not depend on any axioms' in line:
        name=line.split(' does not depend on any axioms',1)[0];axioms[name[1:-1]]=[]
assert set(axioms)=={'E11Critic.cycle5_no_zero_cut','E11Critic.zero_blowup_zero_cut','E11Critic.positive_blowup_needed'}
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values())
result['axioms']=axioms;save()
code,log=run('kernel-ReviewControls',[str(BIN/'leanchecker'),'ReviewControls','-v']);assert code==0,log
code,log=run('reject-MissingPositiveBlowup',[str(BIN/'lean'),'MissingPositiveBlowup.lean'])
assert code!=0 and 'unsolved goals' in log and '⊢ False' in log
assert not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize|Type mismatch|Ambiguous term|\bsorry\b|sorryAx',log),log
result['passed']=True;result['completed_utc']=datetime.now(timezone.utc).isoformat();save()
print(json.dumps({'passed':True,'work':str(out),'steps':len(result['runs']),'axioms':len(axioms)}))
