#!/usr/bin/env python3
"""Bind the review packet, source inputs and copied proof provenance."""
from pathlib import Path
import hashlib,json,datetime
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dumps(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
verification=json.loads((HERE/'verification.json').read_text())
assert verification['passed'] and verification['source_unchanged']
for name,h in verification['source_sha256'].items():assert sha(HERE/(name+'.lean'))==h
inputs=['AGENTS.md','research/pods/2026-10-18/digital-hold-01/CHARTER.txt',
        'research/controls-scope-review-20261018/ASSESSMENT.txt',
        'research/controls-scope-review-20261018/NEXT-GATE.txt',
        'research/controls-scope-review-20261018/AGE-BUDGET.txt',
        'research/controls-scope-review-20261018/COMMENTS.txt',
        'research/controls-scope-review-20261018/age_budget.py',
        'research/adjacent-controls/variable-response/sampled-handoff/RobustHold.lean',
        'research/adjacent-controls/variable-response/sampled-handoff/Capture.lean',
        'research/adjacent-controls/variable-response/sampled-handoff/Handoff.lean',
        'research/adjacent-controls/variable-response/sampled-handoff/verification.json',
        'research/adjacent-controls/variable-response/sampled-handoff/hold-scope.txt',
        'lean-controls/lean-toolchain','lean-controls/lake-manifest.json']
dumps(HERE/'input-sha256.json',{p:sha(WORK/p) for p in inputs})
r=(WORK/'research/adjacent-controls/variable-response/sampled-handoff/RobustHold.lean').read_text()
s=(HERE/'DigitalHold.lean').read_text();segments=[]
for a,b in [('/-- Coordinates chosen','/-- The invariant-coordinate ODE'),('/-- At any face','/-- Arbitrary finite-horizon'),('/-- The cube gives','/-- Actual holding preserves')]:
    fragment=r[r.index(a):r.index(b)];assert fragment in s
    segments.append({'start_marker':a,'end_marker_exclusive':b,'sha256':hashlib.sha256(fragment.encode()).hexdigest(),'exact_fragment_present':True})
dumps(HERE/'provenance.json',{'origin':'research/adjacent-controls/variable-response/sampled-handoff/RobustHold.lean','origin_sha256':hashlib.sha256(r.encode()).hexdigest(),'copied_segments':segments,'changed_part':'finite_barrier was adapted to finite_prefix_barrier, using a left derivative and an entire-prefix boundary premise. Other digital proof source and the two-cell witness are new.'})
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
(HERE/'FREEZE.txt').write_text('SOURCE FREEZE '+now+'\nBoth final local modules and the recorded verification passed.\nIndependent acceptance is pending. Do not change source or packet files without\na named repair and a new verification run and manifest.\nReplay: python3 research/pods/2026-10-18/digital-hold-01/builder/verify.py\nThe reviewer should copy sources into critic-owned scratch space before replay.\nGeneral existence is outside the Lean claim. See MODEL-AND-EXISTENCE.txt.\n')
excluded={'build','fresh-replay','__pycache__'}
files=[p for p in HERE.rglob('*') if p.is_file() and not excluded.intersection(p.relative_to(HERE).parts) and p.name!='artifact-sha256.json']
dumps(HERE/'artifact-sha256.json',{'frozen_utc':now,'status':'builder frozen; independent acceptance pending','files':{str(p.relative_to(HERE)):sha(p) for p in sorted(files)}})
manifest=json.loads((HERE/'artifact-sha256.json').read_text())
assert all(sha(HERE/p)==h for p,h in manifest['files'].items())
print(json.dumps({'frozen_utc':now,'files':len(files),'manifest_sha256':sha(HERE/'artifact-sha256.json'),'source_sha256':verification['source_sha256'],'verification_passed':True}))
