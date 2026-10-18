#!/usr/bin/env python3
"""Check the model-to-vertex boundary using one intentional feedback mutation."""
from pathlib import Path
import hashlib,json,re,subprocess,tempfile,time
from lean_runtime import runtime
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'evidence/model-bridge';OUT.mkdir(exist_ok=True)
source=ROOT/'LeanControls/SaturatedLag.lean';original=source.read_text()
old='def input (z : State) : ℝ := -z 0 - 3 * z 1 - 2 * z 2'
new='def input (z : State) : ℝ := -z 0 - 3 * z 1 - 3 * z 2'
assert original.count(old)==1
mutated=original.replace(old,new);lake,env=runtime(ROOT)
report={'status':'running','original_sha256':hashlib.sha256(original.encode()).hexdigest(),
 'mutation':'acceleration feedback coefficient 2 -> 3; old polynomial vertex certificates retained',
 'not_a_theorem':'A negative artifact test, not proof of physical unsafety or instability.','runs':[]}
try:
 with tempfile.TemporaryDirectory(prefix='lean-model-bridge-') as tmp:
  for label,blob in [('positive',original),('mutated',mutated)]:
   path=Path(tmp)/'SaturatedLag.lean';path.write_text(blob);command=[lake,'env','lean',str(path)]
   start=time.perf_counter();r=subprocess.run(command,cwd=ROOT,env=env,capture_output=True,text=True,timeout=180)
   log=r.stdout+r.stderr;(OUT/f'{label}.log').write_text(log)
   errors=re.findall(r'SaturatedLag\.lean:(\d+):\d+: error: ([^\n]+)',log)
   report['runs'].append({'label':label,'source_sha256':hashlib.sha256(blob.encode()).hexdigest(),
     'exit_code':r.returncode,'seconds':time.perf_counter()-start,'errors':errors,'command':command})
   if label=='positive': assert r.returncode==0,log
   else:
    assert r.returncode!=0 and len(errors)>=4,log
    # These are the four explicit plant-to-generated-transition identities.
    lines=blob.splitlines(); theorem_lines=[i+1 for i,s in enumerate(lines) if re.match(r'theorem (quarter|full)_(lower|upper)_vertex',s)]
    assert len(theorem_lines)==4,theorem_lines
    assert all(any(lo <= int(err[0]) < lo+12 for err in errors) for lo in theorem_lines),errors
 report['status']='passed'
except Exception as e:
 report['status']='failed';report['error']=str(e);raise
finally:
 (OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print('Original model accepted; changed feedback rejected at all four model-to-vertex bridges.')
