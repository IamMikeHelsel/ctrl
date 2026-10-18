import subprocess,time,json,concurrent.futures,os
from pathlib import Path
p=Path(__file__).resolve().parent
lean=p.parents[3]/'.tools/elan/toolchains/leanprover--lean4---v4.33.1/bin/lean'
def run(name):
    cmd=[str(lean),f'{name}Replay.lean']
    t=time.perf_counter()
    try:
        r=subprocess.run(cmd,cwd=p,env={**os.environ,'LEAN_PATH':str(p)},capture_output=True,text=True,timeout=90)
        out={'exit_code':r.returncode,'seconds':time.perf_counter()-t}
        (p/f'{name.lower()}-replay.log').write_text(r.stdout+r.stderr)
    except subprocess.TimeoutExpired as e:
        out={'exit_code':None,'timeout_seconds':90,'seconds':time.perf_counter()-t}
        (p/f'{name.lower()}-replay.log').write_bytes((e.stdout or b'')+(e.stderr or b''))
    return name,out
results=dict(run(n) for n in ['Baseline','Sparse'])
(p/'local-replay.json').write_text(json.dumps({'kind':'Local Lean 4.33.1 proof elaboration and kernel checking of three rfl examples; not official evaluator instruction counts','results':results},indent=2)+'\n')
print(json.dumps(results,indent=2))
