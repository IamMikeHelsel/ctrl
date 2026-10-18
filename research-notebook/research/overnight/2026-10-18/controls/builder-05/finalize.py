"""Freeze this builder batch only after successful verification. Does not accept it."""
from pathlib import Path
import datetime,hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'artifact-sha256.json').exists(),'Already frozen'
report=json.loads((HERE/'verification.json').read_text());assert report['passed']
for f,h in json.loads((HERE/'pre-run-freeze-02.json').read_text())['files'].items():assert sha(HERE/f)==h,f
subprocess.run([sys.executable,str(HERE/'setup.py')],check=True)
assert sum(len(v) for v in json.loads((HERE/'exact-witness-values.json').read_text())['rows'].values())==16
for m,v in report['sources'].items():assert sha(HERE.parents[4]/v['path'])==v['sha256'],m
(HERE/'FINAL-REPORT.txt').write_text(f'''BUILDER 05 COMPLETE — INDEPENDENT REVIEW REQUIRED

The same-actual-trajectory FIR return and hold statement compiled from fresh
sources. The physical terminal deadline is 3.42 s. The 1.7 s numerical task is
not a proved physical deadline. Read CLAIMS.txt and FIRHold.lean for scope.

Verified in this builder batch
- {report['fresh_local_module_count']} local modules compiled into a new temporary folder.
- {report['all_local_declaration_count']} local declarations passed the axiom and unsafe-code audit.
- {len(report['kernel_modules'])} key modules passed separate leanchecker replay.
- {report['negative_count']} false clients failed at intended False goals with imports resolved.
- Two actual moving witness families are checked: constant nonzero bias, and
  changing response with a prescribed changing bounded disturbance.
- Sixteen exact rational anchor states satisfy the stated physical ODE.
- Wrong unshifted inputs require jerk -1/48 m/s^3 where shifted actual jerk is zero.
- All 55 inherited source modules match their two accepted source records.
- Both parent artifact manifests were checked again without a changed byte.

No old source, toolchain pin, manuscript, Git checkout or parent artifact was
modified. Development failures and the verifier text-scanner false positive
remain in this folder. The first verifier did not reach proof compilation; the
repaired verifier and all-declaration audit passed. See verification-errata.txt.

The builder does not accept its own result. A fresh critic must inspect the
statements, inherited state and time shift, witnesses, source provenance, and
verification evidence. No new optimizer, hardware result, or novelty is claimed.

Next decision
If independently accepted, this closes the declared FIR-to-terminal-hold gap.
Do not continue adding scalar lemmas merely to increase coverage. The shorter
physical deadline, implementation model, coupled robot and hardware acceptance
remain separate questions. Root owns any manuscript and repository update.
''')
files={}
for p in sorted(HERE.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(HERE)
 if any(x in {'build','__pycache__'} or x.startswith('fresh-') for x in rel.parts):continue
 if rel.as_posix()=='artifact-sha256.json':continue
 files[rel.as_posix()]={'sha256':sha(p),'bytes':p.stat().st_size}
manifest={'frozen_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'builder complete; independent review pending','files':files}
(HERE/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'manifest_sha256':sha(HERE/'artifact-sha256.json'),'files':len(files),'bytes':sum(v['bytes'] for v in files.values()),'main_source_sha256':sha(HERE/'FIRHold.lean'),'witness_source_sha256':sha(HERE/'FIRHoldWitness.lean')}))
