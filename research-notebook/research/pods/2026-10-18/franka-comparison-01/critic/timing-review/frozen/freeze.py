from pathlib import Path
import hashlib,json,datetime,difflib
P=Path(__file__).resolve().parent;W=P.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not (P/'frozen-manifest.json').exists()
r=json.loads((P/'verification.json').read_text());assert r['passed'] and r['source_unchanged'] and r['prior_frozen_preserved']
assert sha(P/'verify.py')==r['verifier_sha256']
assert len(r['steps'])==23 and len(r['axioms'])==110
for m,h in r['source_sha256'].items():
 p=(P/'inputs' if m in ['DigitalHold','WeightedEntry','ClearancePolicy'] else P)/(m+'.lean')
 assert sha(p)==h and sha(P/'fresh-replay'/(m+'.lean'))==h
for x in json.loads((P/'INPUTS.json').read_text()):assert sha(W/x['source'])==sha(P/x['copy'])==x['sha256']
for x in json.loads((P/'PINS.json').read_text()):assert sha(W/x['path'])==x['sha256']
for x in json.loads((P/'SOURCE-DERIVATION.json').read_text()):assert sha(P/x['source'])==x['source_sha256'] and sha(P/x['derived'])==x['derived_sha256']
counts={}
old=W/'research/pods/2026-10-18/method-transfer-01/controls'
for n,h in r['prior_frozen_manifests'].items():
 p=old/n/'frozen-manifest.json';assert sha(p)==h;files=json.loads(p.read_text())['files']
 assert all(sha(p.parent/f)==v for f,v in files.items());counts[n]=len(files)
for n,h in json.loads((P/'minimal-gate/manifest.json').read_text()).items():assert sha(P/'minimal-gate'/n)==h
assert sha(P/'screen.py')==json.loads((P/'screen-results.json').read_text())['source_sha256']
for x in r['steps']:
 assert x['passed'] and sha(P/'verification-logs'/(x['label']+'.log'))==x['log_sha256']
 if x['label'].startswith('reject-'):
  raw=(P/'verification-logs'/(x['label']+'.log')).read_text().lower()
  assert not any(s in raw for s in ['unknown identifier','unknown module','no such file','ambiguous'])
(P/'NEGATIVE-REVIEW.txt').write_text('''All eight saved rejection logs were read after replay completed.
The dropped-pending-overlap mutation leaves an unjustified L*a upper bound.
The renewed-stamp mutation breaks causality at startup and reduces the exact
second-dispatch boundary claim to False. These are source-sensitivity tests.
All six separate false assertions reduce to False after exact arithmetic.
No ambiguous-name, missing import, unknown identifier or missing file caused
a rejection. No aggregate bound failure is called a realized unsafe plant.
Independent diagnostic review remains separate from this builder check.
''')
private=sum(len(v['private']) for v in r['declaration_inventory'].values())
summary=f'''BUILDER VERIFICATION — INDEPENDENT ACCEPTANCE PENDING
Seven local research source builds passed from a new copied-source directory.
Only pinned external Mathlib artifacts were reused; no local proof cache.
All 110 direct public theorem/lemma axiom closures contain only propext,
Classical.choice and Quot.sound. Private declarations in these sources: {private}.
Seven separate module kernel checks passed. Eight semantic rejection controls
passed: two source mutations, six false exact assertions. All 23 steps passed.
All C1-C8 frozen files remain unchanged: {counts}.
The minimal compiled gate, two proof-development failures and one pre-replay
pin setup failure are retained. No verifier remains running. All negative
logs were inspected; their reason is semantic, not import/name/setup failure.
'''
(P/'VERIFICATION-SUMMARY.txt').write_text(summary)
s=(P/'REPORT.txt').read_text().replace('Fresh verification in progress; independent review pending.','Frozen after builder verification; independent review pending.')
oldtext='Pending final fresh replay. The main development theorem and exact clock\ncompile. All local dependencies will be copied and rebuilt; axiom closures,\nseparate kernel checks and semantic negatives are required before freeze.\nNo self-acceptance is claimed.'
new='All seven fresh copied-source builds, 110 allowed-only public axiom closures,\nseven separate kernels and eight semantic rejection controls passed. All 23\nrecorded steps passed. The negative logs were read and contain no name/import\nsetup failures. Two proof failures and one pre-replay pin setup failure are\npreserved. The C1-C8 freezes and all toolchain pins remain unchanged.\nSee verification.json and VERIFICATION-SUMMARY.txt. No self-acceptance.'
assert oldtext in s;(P/'REPORT.txt').write_text(s.replace(oldtext,new))
files={str(p.relative_to(P)):sha(p) for p in sorted(P.rglob('*')) if p.is_file() and p.suffix in {'.lean','.py','.json','.txt','.log'} and 'build' not in p.relative_to(P).parts and p.name!='frozen-manifest.json'}
out={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'T1 conditional 1 kHz holding clearance with illustrative .5 ms delay and 1.5 ms total age; no physical constructor or C6/C8 hybrid timing extension. Independent review pending.','files':files}
(P/'frozen-manifest.json').write_text(json.dumps(out,indent=2)+'\n');assert all(sha(P/f)==h for f,h in files.items())
print(json.dumps({'manifest_sha256':sha(P/'frozen-manifest.json'),'report_sha256':sha(P/'REPORT.txt'),'files':len(files),'frozen_utc':out['frozen_utc']}))
