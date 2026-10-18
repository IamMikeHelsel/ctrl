#!/usr/bin/env python3
"""Rebuild audit modules and replay them; inherited algebra products are reused.
Whole-bundle fresh verification is the coordinator's separate task.
"""
from pathlib import Path
import os,subprocess,json,hashlib,datetime
B=Path(__file__).resolve().parent
R=Path('/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes')
L=R/'lean-controls'; old=R/'research/overnight/2026-10-18/geometric-unity/builder-05'
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');lake=str(R/'.tools/elan/bin/lake')
lean=Path(subprocess.check_output([lake,'env','which','lean'],cwd=L,env=env,text=True).strip())
env['PATH']=str(lean.parent)+os.pathsep+env['PATH']
paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=L,env=env,text=True).strip().split(':')
env['LEAN_PATH']=':'.join([str(B),str(B.parent/'algebra'),str(B.parent/'spin/cache'),str(old/'cache/fresh-01')]+[str((L/p).resolve()) for p in paths])
result={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'boundary':'Four modules rebuilt; existing actual algebra and pinned mathlib products reused. Not a whole-bundle fresh replay.','steps':[]}
for m in ['VolumeTwist','VolumeTwistActual','QuadraticTwist','GeneralBoost']:
    for kind,cmd in [('compile',[str(lean),'-o',str(B/(m+'.olean')),str(B/(m+'.lean'))]),('kernel',[str(lean.with_name('leanchecker')),m,'-v'])]:
        p=subprocess.run(cmd,cwd=B,env=env,text=True,capture_output=True)
        log=B/(kind+'-'+m+'.log'); log.write_text(p.stdout+p.stderr)
        result['steps'].append({'module':m,'kind':kind,'exit_code':p.returncode,'log':log.name})
        if p.returncode: print(log.read_text()); raise SystemExit(p.returncode)
result['lean_version']=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip()
result['source_hashes']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [B/'VolumeTwist.lean',B/'VolumeTwistActual.lean',B/'QuadraticTwist.lean',B/'GeneralBoost.lean']}
result['status']='pass'
(B/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
