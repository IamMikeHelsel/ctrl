"""Bind C2 sources and completed evidence for independent review."""
from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'frozen-manifest.json').exists(),'Do not overwrite a frozen milestone.'
report=json.loads((HERE/'verification.json').read_text())
assert report['passed'] and report['source_unchanged'] and report['prior_frozen_inputs_preserved']
assert sha(HERE/'verify.py')==report['verifier_sha256']
for m,h in report['source_sha256'].items():
 p=(HERE/'inputs' if m=='DigitalHold' else HERE)/(m+'.lean')
 assert sha(p)==h and sha(HERE/'fresh-replay'/(m+'.lean'))==h
for row in json.loads((HERE/'INPUTS.json').read_text()):
 assert sha(WORK/row['source'])==sha(HERE/row['copy'])==row['sha256']
prior_counts={}
for name,p,expected in [
 ('shortlist',HERE.parent/'PREFLIGHT-MANIFEST.json','e87a250aff21e22ac7377a012ce6a282e016316484fc73b954a4ff1c23b6d8d9'),
 ('C1',HERE.parent/'milestone-01/frozen-manifest.json','86a05aa25625d1054a2213a3599b703d31db5341e365f0e5a79e020dfd937186')]:
 assert sha(p)==expected
 d=json.loads(p.read_text())
 pairs=d['files'].items() if 'files' in d else [(e['path'],e['sha256']) for e in d['entries']]
 pairs=list(pairs)
 assert all(sha(p.parent/f)==h for f,h in pairs)
 prior_counts[name]=len(pairs)
for step in report['steps']:
 assert step['passed'] and sha(HERE/'verification-logs'/(step['label']+'.log'))==step['log_sha256']
negative=[s for s in report['steps'] if s['label'].startswith('reject-')]
builds=[s for s in report['steps'] if s['label'].startswith('build-')]
kernels=[s for s in report['steps'] if s['label'].startswith('kernel-')]
assert len(negative)==6 and len(builds)==len(kernels)==3
summary=f'''BUILDER VERIFICATION COMPLETED
Complete local copied-source closure: {len(builds)} modules freshly rebuilt.
Separate kernel replays: {len(kernels)}; all passed.
Audited theorem closures: {len(report['axioms'])}; only propext, Classical.choice, Quot.sound.
Semantic rejection controls: {len(negative)}; all rejected as intended.
Total saved steps: {len(report['steps'])}; all passed.
Preserved old freezes: {prior_counts}; accepted DigitalHold and copy also unchanged.
Existing pinned external package artifacts were reused; see verification.json.
Independent acceptance is pending. No verification job remains running.
'''
(HERE/'VERIFICATION-SUMMARY.txt').write_text(summary)
files={str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*'))
 if p.is_file() and p.suffix in {'.lean','.py','.txt','.json','.log'}
 and 'build' not in p.relative_to(HERE).parts and p.name!='frozen-manifest.json'}
manifest={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'C2 finite-entry builder milestone. Sources and evidence frozen for independent review. Build caches excluded.',
 'files':files}
(HERE/'frozen-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'manifest_sha256':sha(HERE/'frozen-manifest.json'),'report_sha256':sha(HERE/'REPORT.txt'),
 'files':len(files),'frozen_utc':manifest['frozen_utc']}))
