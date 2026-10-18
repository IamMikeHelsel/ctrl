"""Dispatch one bounded numerical scout through the existing Sparky SSH alias."""
from pathlib import Path
import datetime,hashlib,json,shlex,subprocess
HERE=Path(__file__).resolve().parent
source=(HERE/'free_slope_scout.py').read_bytes();digest=hashlib.sha256(source).hexdigest()
remote='/home/mike/research-method-transfer-20261018/free-slope-scout-'+digest[:12]
ssh=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=8','sparky.local']
subprocess.run(ssh+['mkdir -p '+shlex.quote(remote)],check=True,timeout=15)
subprocess.run(ssh+['cat > '+shlex.quote(remote+'/free_slope_scout.py')],input=source,check=True,timeout=15)
command='cd '+shlex.quote(remote)+' && echo $$ > runner.pid && exec timeout --signal=TERM --kill-after=5s 45s python3 free_slope_scout.py'
job={'job':'free-slope-scout-01','source_sha256':digest,'host':'sparky.local','remote_directory':remote,
 'command_argv':ssh+[command],'resource_cap':'one CPU process,45second runtime plus5second termination grace,no GPU',
 'remote_process_identity':'runner.pid in unique source-hash directory; exec replaces shell with timeout supervisor',
 'termination':'GNU timeout sends TERM at45seconds and KILL5seconds later; do not terminate unrelated processes',
 'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'running',
 'scope':'numerical scalar proposal screen only'}
(HERE/'free-slope-scout-job.json').write_text(json.dumps(job,indent=2)+'\n')
r=subprocess.run(ssh+[command],capture_output=True,text=True,timeout=60)
(HERE/'free-slope-scout.stdout.txt').write_text(r.stdout)
(HERE/'free-slope-scout.stderr.txt').write_text(r.stderr)
job.update(exit_code=r.returncode,completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='completed' if r.returncode==0 else 'failed')
if r.returncode==0:
 data=json.loads(r.stdout);assert data['source_sha256']==digest
 (HERE/'free-slope-scout-results.json').write_text(r.stdout)
 job['remote_python_pid']=data['pid'];job['output_sha256']=hashlib.sha256(r.stdout.encode()).hexdigest()
 print(json.dumps({'cases':data['cases'],'targets':data['targets'],'local_exact_control':data['local_exact_control']},indent=2))
else:print(r.stderr)
(HERE/'free-slope-scout-job.json').write_text(json.dumps(job,indent=2)+'\n')
raise SystemExit(r.returncode)
