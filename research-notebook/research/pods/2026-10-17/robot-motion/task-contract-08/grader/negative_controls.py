#!/usr/bin/env python3
from pathlib import Path
import os,json,subprocess,hashlib
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5];BUILD=HERE/'build'
report=json.loads((HERE/'proof-review.json').read_text())
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=WORK/'lean-controls',env=env,text=True).strip()
env['LEAN_PATH']=':'.join([str(BUILD)]+report['external_cache_paths'])
folder=HERE/'negative-controls';folder.mkdir(exist_ok=True)
head='import ReviewIntegrationWitnesses\nimport ReviewTaskWitnesses\nopen RobotMotion RobotMotion.TaskContract\nnoncomputable section\n'
controls={
 'ShortDeadline':head+'example : (11/50+4*(1/5):ℝ) ≤ 31/50 := by norm_num\n',
 'PendingHistoryComplete':head+'example : CompleteBy (1/5) 0 [(1,1/50)] := by norm_num [CompleteBy]\n',
 'GuardImpliesAcceleration':head+'example (accepted : check (1/5) (15/2) 0 [(11/50,1/50),(13/25,-1/50)] = true) : |acceleration (1/5) [(11/50,1/50),(13/25,-1/50)] (77/100)| ≤ 1/2 := by norm_num [acceleration,response,F2,P]\n',
 'HorizonBeforeDeadline':head+'example : (51/50:ℝ) ≤ 1 := by norm_num\n',
 'HalfwayAlreadyArrived':head+'example : |position 0 (1/5) [(11/50,1/50)] (31/50) - (1/50:ℝ)| ≤ 1/5000 := by norm_num [position,response,F0,P]\n'
}
results=[]
for name,source in controls.items():
 p=folder/(name+'.lean');p.write_text(source)
 run=subprocess.run([lean,str(p)],cwd=BUILD,env=env,capture_output=True,text=True)
 log=folder/(name+'.log');log.write_text(run.stdout+run.stderr)
 assert run.returncode!=0 and 'error:' in log.read_text(),name
 assert 'unknown module' not in log.read_text() and 'unknown identifier' not in log.read_text(),name
 results.append({'name':name,'rejected':True,'exit_code':run.returncode,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
(HERE/'negative-controls.json').write_text(json.dumps({'passed':True,'controls':results,'scope':'All false acceptance assertions rejected. Independent positive witnesses establish why the relevant implication fails; compile rejection alone is not a theorem of impossibility.'},indent=2)+'\n')
print(json.dumps(results,indent=2))
