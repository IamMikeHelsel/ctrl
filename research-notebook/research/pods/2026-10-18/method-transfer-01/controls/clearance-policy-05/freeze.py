"""Bind the completed C5 builder evidence; refuse to overwrite a freeze."""
from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'frozen-manifest.json').exists()
report=json.loads((HERE/'verification.json').read_text())
assert report['passed'] and report['source_unchanged'] and report['prior_frozen_inputs_preserved']
assert sha(HERE/'verify.py')==report['verifier_sha256']
for m,h in report['source_sha256'].items():
 p=(HERE if m.startswith('Clearance') else HERE/'inputs')/(m+'.lean')
 assert sha(p)==h and sha(HERE/'fresh-replay'/(m+'.lean'))==h
for row in json.loads((HERE/'INPUTS.json').read_text()):
 assert sha(WORK/row['source'])==row['sha256']
 assert sha(HERE/row['copy'])==row['sha256']
for row in json.loads((HERE/'PREFLIGHT-SOURCES.json').read_text()):assert sha(WORK/row['source'])==row['sha256']
records=[
 ('shortlist',HERE.parent/'PREFLIGHT-MANIFEST.json','e87a250aff21e22ac7377a012ce6a282e016316484fc73b954a4ff1c23b6d8d9'),
 ('C1',HERE.parent/'milestone-01/frozen-manifest.json','86a05aa25625d1054a2213a3599b703d31db5341e365f0e5a79e020dfd937186'),
 ('C2',HERE.parent/'finite-entry-02/frozen-manifest.json','c78f5b409eda906a36efeb1b73cf3f75bbecef83bcdf9764eb8c4dd3d46ee52e'),
 ('C3',HERE.parent/'adaptive-admission-03/frozen-manifest.json','7d56bd57f0a340107ad04e2c3b0e06aa7a11329757fa241598845294a58a302a'),
 ('C4',HERE.parent/'delayed-entry-04/frozen-manifest.json','529bc733f386713d74eb2bfe039b945b5a339b41f9c5afffeb43bf997ad9e5ea'),
 ('root-preflight',HERE.parents[1]/'root-review/interval-center-preflight/manifest.json','0a09887e53184b49a54f07c63b27feb2f652bc7286052506368bf9815d6af15d'),
 ('critic-gate',HERE.parents[1]/'critic/milestone-09/clearance-policy-gate/manifest.json','ffbb1cabec9be390ac9cd5683adda3ca818f7e3ccd9b41d483277a5ec7423a78'),
 ('delayed-handoff',WORK/'research/pods/2026-10-18/recovery-handoff-02/handoff-builder/artifact-sha256.json','0ca3f54c0d77ff244866bb5a861c6d701749594d6d155c87ba9ab7338e23276e')]
counts={}
for name,p,h in records:
 assert sha(p)==h
 d=json.loads(p.read_text())
 pairs=list(d['files'].items()) if 'files' in d else [(e['path'],e['sha256']) for e in d['entries']]
 assert all(sha(p.parent/f)==v for f,v in pairs)
 counts[name]=len(pairs)
for step in report['steps']:
 assert step['passed'] and sha(HERE/'verification-logs'/(step['label']+'.log'))==step['log_sha256']
arithmetic=json.loads((HERE/'arithmetic.json').read_text())
assert sha(HERE/'arithmetic.py')==arithmetic['script_sha256']
assert len(arithmetic['affine_corner_certificate'])==120
negative=[s for s in report['steps'] if s['label'].startswith('reject-')]
builds=[s for s in report['steps'] if s['label'].startswith('build-')]
kernels=[s for s in report['steps'] if s['label'].startswith('kernel-')]
assert len(negative)==9 and len(builds)==len(kernels)==9
summary=f'''BUILDER VERIFICATION COMPLETED
Complete local copied-source closure: {len(builds)} modules freshly rebuilt.
Separate kernel replays: {len(kernels)}; all passed.
Audited theorem closures: {len(report['axioms'])}; only propext, Classical.choice, Quot.sound.
Semantic rejection controls: {len(negative)}; all rejected as intended.
Total saved steps: {len(report['steps'])}; all passed.
Preserved prior frozen files: {counts}; exact old source/template inputs also unchanged.
Existing pinned external package artifacts were reused; see verification.json.
Independent acceptance is pending. No verification job remains running.
'''
(HERE/'VERIFICATION-SUMMARY.txt').write_text(summary)
files={str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*'))
 if p.is_file() and p.suffix in {'.lean','.py','.txt','.json','.log'}
 and 'build' not in p.relative_to(HERE).parts and p.name!='frozen-manifest.json'}
manifest={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'C5 interval-center whole-horizon clearance builder packet; source and evidence frozen for independent review. Build caches excluded.',
 'files':files}
(HERE/'frozen-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert all(sha(HERE/f)==h for f,h in files.items())
print(json.dumps({'manifest_sha256':sha(HERE/'frozen-manifest.json'),
 'report_sha256':sha(HERE/'REPORT.txt'),'files':len(files),'frozen_utc':manifest['frozen_utc']}))
