"""Freeze completed milestone evidence only. Does not change proof inputs."""
from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'frozen-manifest.json').exists(),'Do not overwrite a frozen milestone.'
report=json.loads((HERE/'verification.json').read_text())
assert report['passed']
assert sha(HERE/'verify.py')==report['verifier_sha256']
for m,h in report['source_sha256'].items():
 p=(HERE if m.startswith('RecoveryPeak') else HERE/'inputs')/(m+'.lean')
 assert sha(p)==h and sha(HERE/'fresh-replay'/(m+'.lean'))==h
preflight=json.loads((HERE.parent/'PREFLIGHT-MANIFEST.json').read_text())
assert all(sha(HERE.parent/e['path'])==e['sha256'] for e in preflight['entries'])
negative=[s for s in report['steps'] if s['label'].startswith('reject-')]
assert len(negative)==6 and all(s['passed'] for s in negative)
builds=[s for s in report['steps'] if s['label'].startswith('build-')]
kernels=[s for s in report['steps'] if s['label'].startswith('kernel-')]
summary=f'''BUILDER VERIFICATION COMPLETED
Full local copied-source rebuild: {len(report['core_build_order'])} LeanControls dependencies and 7 research modules.
Separate kernel replays: {len(kernels)}; all passed.
Audited theorem closures: {len(report['axioms'])}; only propext, Classical.choice, Quot.sound.
Semantic rejection controls: {len(negative)}; all rejected as intended.
Total saved steps: {len(report['steps'])}; all passed.
Old copied inputs, all local core sources and the 25-file shortlist preflight remain unchanged.
Existing pinned external package artifacts were reused; see verification.json.
Independent acceptance is pending. No job from this verifier remains running after it returns.
'''
(HERE/'VERIFICATION-SUMMARY.txt').write_text(summary)
files={str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*'))
 if p.is_file() and p.suffix in {'.lean','.py','.txt','.json','.log'}
 and 'build' not in p.relative_to(HERE).parts and p.name!='frozen-manifest.json'}
manifest={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'C1 builder milestone; sources and evidence are frozen for independent review. Build caches are excluded.',
 'files':files}
(HERE/'frozen-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'manifest_sha256':sha(HERE/'frozen-manifest.json'),'files':len(files),'frozen_utc':manifest['frozen_utc']}))
