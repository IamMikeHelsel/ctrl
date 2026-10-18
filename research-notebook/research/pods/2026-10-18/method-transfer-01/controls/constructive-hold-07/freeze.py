"""Freeze C7 evidence after all verification steps pass. No overwrite."""
from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5];BASE=WORK/'lean-controls'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'frozen-manifest.json').exists()
r=json.loads((HERE/'verification.json').read_text())
assert all(r[k] for k in ['passed','source_unchanged','core_source_unchanged','old_inputs_preserved','preflight_preserved','prior_frozen_inputs_preserved'])
assert sha(HERE/'verify.py')==r['verifier_sha256']
for m,h in r['source_sha256'].items():
 p=(HERE if m.startswith('Constructive') else HERE/'inputs')/(m+'.lean')
 assert sha(p)==h and sha(HERE/'fresh-replay'/(m+'.lean'))==h
for m,h in r['core_source_sha256'].items():
 p=Path(m.replace('.','/')+'.lean')
 assert sha(BASE/p)==h and sha(HERE/'fresh-replay'/p)==h
for f in ['INPUTS.json','PREFLIGHT-SOURCES.json']:
 for row in json.loads((HERE/f).read_text()):
  assert sha(WORK/row['source'])==row['sha256']
  if 'copy' in row:assert sha(HERE/row['copy'])==row['sha256']
trace=json.loads((HERE/'witness-trace.json').read_text())
assert trace['script_sha256']==sha(HERE/'witness_trace.py')
assert all(sha(HERE/f)==h for f,h in trace['source_sha256'].items())
records=[
 ('C1',HERE.parent/'milestone-01/frozen-manifest.json','86a05aa25625d1054a2213a3599b703d31db5341e365f0e5a79e020dfd937186'),
 ('C2',HERE.parent/'finite-entry-02/frozen-manifest.json','c78f5b409eda906a36efeb1b73cf3f75bbecef83bcdf9764eb8c4dd3d46ee52e'),
 ('C3',HERE.parent/'adaptive-admission-03/frozen-manifest.json','7d56bd57f0a340107ad04e2c3b0e06aa7a11329757fa241598845294a58a302a'),
 ('C4',HERE.parent/'delayed-entry-04/frozen-manifest.json','529bc733f386713d74eb2bfe039b945b5a339b41f9c5afffeb43bf997ad9e5ea'),
 ('C5',HERE.parent/'clearance-policy-05/frozen-manifest.json','ca1aa5fd23f1f0d9e3456237712fa90f2c5093a0eb2e1bc63c4b546e4b427691'),
 ('C6',HERE.parent/'detector-bridge-06/frozen-manifest.json','133ccaf800b1699c2f126cfaf12d65ec63f460681a3a9de58607eb5d37c8313b')]
counts={}
for name,p,h in records:
 assert sha(p)==h
 files=json.loads(p.read_text())['files'];assert all(sha(p.parent/f)==v for f,v in files.items())
 counts[name]=len(files)
for row in r['steps']:assert row['passed'] and sha(HERE/'verification-logs'/(row['label']+'.log'))==row['log_sha256']
builds=[s for s in r['steps'] if s['label'].startswith('build-')]
kernels=[s for s in r['steps'] if s['label'].startswith('kernel-')]
negatives=[s for s in r['steps'] if s['label'].startswith('reject-')]
assert len(builds)==len(kernels)==45 and len(negatives)==10
summary=f'''BUILDER VERIFICATION COMPLETED — INDEPENDENT ACCEPTANCE PENDING
Complete local closure: 31 LeanControls modules and 14 research modules.
Fresh copied-source builds: {len(builds)}; separate kernel replays: {len(kernels)}.
Audited theorem closures: {len(r['axioms'])}; only propext, Classical.choice, Quot.sound.
Semantic rejection controls: {len(negatives)}; all rejected for the expected reason.
Total saved steps: {len(r['steps'])}; all passed.
Prior frozen files preserved: {counts}; all exact source/template inputs unchanged.
No cached local proof product was used. Existing pinned external package
artifacts were reused. Toolchain and package pins match the accepted C1 run.
Development failures are preserved under attempts/. No verifier remains running.
This is builder verification. It does not accept the result or expand its scope.
'''
(HERE/'VERIFICATION-SUMMARY.txt').write_text(summary)
report=(HERE/'REPORT.txt').read_text().replace(
 'Replay in progress; not yet frozen or independently accepted.',
 'Builder verification complete; frozen for independent review.')
old='Pending final completion. Fresh rebuild and axiom audit have passed. The\nseparate kernel replay and semantic negative controls must finish before\nthis report is frozen. No self-acceptance is claimed.'
new=f"All {len(builds)} fresh copied-source builds, {len(kernels)} separate kernels, and {len(negatives)} semantic rejection\ncontrols passed. The {len(r['axioms'])} audited theorem closures use only propext,\nClassical.choice and Quot.sound. All {len(r['steps'])} recorded steps passed. Previous\nfrozen files and toolchain pins are unchanged. Seven development failures\nare preserved. See verification.json and VERIFICATION-SUMMARY.txt.\nThis is builder evidence; independent acceptance remains pending."
assert old in report
(HERE/'REPORT.txt').write_text(report.replace(old,new))

files={str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*'))
 if p.is_file() and p.suffix in {'.lean','.py','.txt','.json','.log'}
 and 'build' not in p.relative_to(HERE).parts and p.name!='frozen-manifest.json'}
out={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'C7 finite constructed delayed hold from an arbitrary admitted pending prefix. Source and evidence frozen for independent review; build caches excluded.',
 'files':files}
(HERE/'frozen-manifest.json').write_text(json.dumps(out,indent=2)+'\n')
assert all(sha(HERE/f)==h for f,h in files.items())
print(json.dumps({'manifest_sha256':sha(HERE/'frozen-manifest.json'),'report_sha256':sha(HERE/'REPORT.txt'),'files':len(files),'frozen_utc':out['frozen_utc']}))
