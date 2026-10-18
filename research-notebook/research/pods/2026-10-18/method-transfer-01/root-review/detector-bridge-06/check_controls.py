#!/usr/bin/env python3
"""Compile reviewer controls only against the completed independent replay."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
data=json.loads((HERE/'verification.json').read_text())
assert data['passed']
work=HERE/('control-attempt-'+datetime.now(timezone.utc).strftime('%H%M%S'))
work.mkdir()
shutil.copyfile(HERE/'ReviewControls.lean',work/'ReviewControls.lean')
lean=Path(data['steps'][0]['command'][0]); checker=lean.with_name('leanchecker')
env=os.environ.copy();env['LEAN_PATH']=str(work)+':'+data['lean_path']
result={'scope':'Reviewer mathematical controls; no full hybrid theorem','runs':[],
        'source_sha256':hashlib.sha256((work/'ReviewControls.lean').read_bytes()).hexdigest()}
def run(label,args,negative=False):
    start=time.monotonic()
    p=subprocess.run(args,cwd=work,env=env,capture_output=True,text=True,timeout=120)
    raw=p.stdout+p.stderr
    (work/(label+'.log')).write_text(raw)
    ok=p.returncode==0 if not negative else p.returncode!=0 and 'unsolved goals' in raw and not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize',raw)
    result['runs'].append({'label':label,'argv':list(map(str,args)),'exit':p.returncode,'passed':bool(ok),'seconds':time.monotonic()-start})
    (work/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(label,p.returncode,flush=True)
    assert ok,raw
    return raw
out=run('compile',[str(lean),'-o','ReviewControls.olean','ReviewControls.lean'])
axes={n:[s.strip() for s in a.split(',') if s.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
assert len(axes)==3 and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
result['axioms']=axes
run('kernel',[str(checker),'ReviewControls','-v'])
(work/'FalseStoppedGuard.lean').write_text('''import ReviewControls
open DetectorReview LeanControls
example : ClearancePolicy.Guard (earlyState (8/25)) → earlyState (8/25) 1 ≤ 0 := by
  intro hg
  norm_num [earlyState,UncertainLag.heldSolution]
''')
run('reject-stopped-guard',[str(lean),'FalseStoppedGuard.lean'],True)
result['passed']=True
(work/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
