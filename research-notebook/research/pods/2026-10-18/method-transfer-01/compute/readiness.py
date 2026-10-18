"""Read-only snapshot of the existing Sparky connection. No service changes."""
import datetime
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
remote = r'''python3 - <<'REMOTE'
import json,platform,subprocess,importlib.util,os
print(json.dumps({
 'architecture':platform.machine(),
 'python':platform.python_version(),
 'packages':{n:bool(importlib.util.find_spec(n)) for n in ['numpy','scipy','sympy','networkx']},
 'lean_exists':os.path.isfile(os.path.expanduser('~/.elan/bin/lean')),
 'model_processes':subprocess.check_output(['ollama','ps'],text=True).strip(),
 'installed_models':subprocess.check_output(['ollama','list'],text=True).strip(),
 'memory':subprocess.check_output(['free','-h'],text=True).strip(),
 'research_processes':subprocess.check_output(['sh','-c',"ps -eo pid,etime,pcpu,args | grep -E '[/](lean|lake)|python.*method-transfer' | head -20"],text=True).strip()
},indent=2))
REMOTE'''
r = subprocess.run(['ssh','-o','BatchMode=yes','-o','ConnectTimeout=8','sparky.local',remote],capture_output=True,text=True,timeout=25)
out = {'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'connection':'Existing sparky.local SSH alias', 'exit_code':r.returncode,
       'remote':json.loads(r.stdout) if r.returncode==0 else None,
       'error':r.stderr, 'scope':'Reachability and installed tools; no proof-generation benchmark.'}
(HERE/'readiness.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'exit_code':r.returncode,'architecture':out['remote']['architecture'] if out['remote'] else None,'packages':out['remote']['packages'] if out['remote'] else None},indent=2))
