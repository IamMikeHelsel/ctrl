"""Repeat the same fixed outputs; this is not an independent implementation."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent
OUTPUTS=['ruckig-smoke-exports.json','ruckig-smoke-results.json','frozen-fixed-streams.json','frozen-reference-checks.json','frozen-reference-enclosures.json','reference-schedules.json','ruckig-primary-exports.json','ruckig-primary-validation.json','retained-negative-cases.json','metrics.csv','metrics.json','event-states.json','refinement.json','native-hold-replay-input.txt','native-hold-replay.json','hold-jitter-diagnostic.json','input-preservation.json','runtime.json','audit-summary.json']
OUTPUTS.append('scheduler-audit.json')
files=[HERE/name for name in OUTPUTS]+sorted((HERE/'traces').iterdir())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
before={str(p.relative_to(HERE)):sha(p) for p in files}
results=[]
for script in ['ruckig_checks.py','make_references.py','run_comparison.py','audit_results.py']:
    run=subprocess.run([sys.executable,'-B',str(HERE/script)],cwd=HERE,text=True,capture_output=True)
    results.append({'script':script,'returncode':run.returncode,'stdout_sha256':hashlib.sha256(run.stdout.encode()).hexdigest(),'stderr':run.stderr})
    if run.returncode:print(run.stdout,run.stderr);run.check_returncode()
after={str(p.relative_to(HERE)):sha(p) for p in files}
assert before==after,{name:(before[name],after[name]) for name in before if before[name]!=after[name]}
result={'passed':True,'scope':'same-code byte-for-byte reproduction; not independent validation','same_fixed_parameter_cases':72,'resolutions':2,'files_reproduced':len(files),'sha256':after,'scripts':results}
(HERE/'reproduction.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'files_reproduced':len(files),'same_fixed_parameter_cases':72,'resolutions':2},indent=2))
