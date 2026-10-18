from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
R=Path(__file__).resolve().parent;B=R.parents[1]/'controls/constructed-handoff-08'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 v=json.loads((R/'verification.json').read_text());assert v['passed'] and len(v['steps'])==127
 assert len(v['core_build_order'])==31 and len(v['research_build_order'])==27
 assert len(v['axioms'])==314 and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in v['axioms'].values())
 inv=json.loads((R/'independent-audit-inventory.json').read_text());assert inv['public_audit_matches'] and set(inv['full_names'])==set(v['axioms'])
 assert len(inv['private_helpers_checked_in_module_and_public_closures'])==3
 assert v['builder_frozen_manifest_preserved'] and sha(B/'frozen-manifest.json')==v['builder_manifest_sha256']
 assert all(sha(B/f)==h for f,h in json.loads((B/'frozen-manifest.json').read_text())['files'].items())
 assert all(s['passed'] and sha(R/'verification-logs'/(s['label']+'.log'))==s['log_sha256'] for s in v['steps'])
 neg=[]
 for f in sorted((R/'verification-logs').glob('reject-*.log')):
  actual=f.read_text();expected=(B/'verification-logs'/f.name).read_text()
  assert actual.replace(str(R),'<REVIEW>')==expected.replace(str(B),'<REVIEW>'),f.name
  assert not any(t in actual.lower() for t in ['unknown identifier','unknown module','no such file','ambiguous term','sorry'])
  neg.append({'log':f.name,'sha256':sha(f),'builder_semantic_diagnostic_reproduced':True})
 assert len(neg)==10
 (R/'negative-review.json').write_text(json.dumps(neg,indent=2)+'\n')
 (R/'NEGATIVE-REVIEW.txt').write_text((R/'NEGATIVE-REVIEW-DRAFT.txt').read_text().replace('Acceptance still requires independent replay, final source-hash comparison\nand examination of the independent diagnostics.','Independent replay reproduced every diagnostic after only the review path\nwas normalized. All final hashes and source checks passed. The six false\nassertions and four source mutations remain distinct evidence classes.'))
 (R/'STATEMENT-REVIEW.txt').write_text((R/'STATEMENT-REVIEW-DRAFT.txt').read_text().replace('C8 ROOT STATEMENT REVIEW — SOURCE READ, REPLAY PENDING','C8 ROOT STATEMENT REVIEW — ACCEPTED').replace('This is not independent acceptance yet.','Accepted after the independent replay recorded in REPORT.txt.').replace('Full fresh copied-source, axiom, kernel and semantic-negative review still\nrequired before accepting any new endpoint.','The complete fresh copied-source, axiom, kernel and semantic-negative\nreview passed. Exact scope and validation are recorded in REPORT.txt.'))
 (R/'REPORT.txt').write_text('''C8 INDEPENDENT REVIEW — ACCEPTED

LeanControls.ConstructedHandoff.exists_assembly constructs one finite causal
recovery/detector/pending/holding path for each supplied C6 braking execution,
valid old readings, arbitrary finite N>=2 and bounded future cell choices.
It derives the pending contract, retains the entire physical prefix and its
acceleration, preserves original sample/arrival clocks, and generates later
readings from the constructed path. It assumes no future hybrid execution,
invariant or aggregate feedback mismatch. The full-time forward ceiling is
3013722449/20100000000m, about149.93644mm.

Acceptance is limited to the actual statements in STATEMENT-REVIEW.txt and
builder CLAIMS.txt. The stronger supplied C6 input stays explicit. The old
recovery join retains phase-open regularity. The construction is finite,
scalar, and uses fixed.5ms sampling and.5ms delay, with piecewise-constant
future rate/target-error cells. No lower travel limit, precision rest,
infinite plant execution, Franka compatibility or hardware result follows.
The combined k632 witness proves nonemptiness and a positive-speed handoff;
its constant old target does not demonstrate a loss/restoration event.

Independent verification
The reviewer read the full new sources, exact input contract and combined
witness before freeze. Those bytes still match the freeze. A separate fresh
copy rebuilt31 local dependency modules and27 research modules. All314
public theorem closures have only propext, Classical.choice and Quot.sound.
All58 separate module kernel checks passed. The127 recorded steps include
ten expected rejections: six false assertions and four source-sensitivity
mutations. Root read every diagnostic; independent diagnostics reproduce the
builder's mathematical goals after path normalization. No setup or ambiguity
failure was accepted as a mathematical rejection.

An independent visibility-aware inventory matches all314 public audit names.
Root initially counted three PRIVATE ComparisonEnvelope helpers as exported
names. That diagnostic assumption failed. Source inspection corrected the
inventory: the private helpers are already checked in their module and via
public dependency closures. A proposed extra direct-name audit was never run.
The original diagnostic record and abandoned script remain in attempts/.
This was a reviewer inventory correction, not a builder proof defect.

All283 frozen builder bindings, earlierC1-C7 inputs, toolchain pins and local
source hashes remain intact. Only existing pinned package artifacts were
reused. No cached local research or LeanControls object supplied a fresh
source build. Seven builder development failures remain preserved. Main
library CI, numerical evidence, novelty and physical acceptance are separate.

Evidence: verification.json, independent-audit-inventory.json,
negative-review.json, replay.py, REPLAY-ADAPTATION.patch, and fresh-replay/
with its source copies. Frozen-manifest.json excludes compiled products.
''')
 allowed={'.py','.json','.txt','.log','.patch','.lean'}
 files={str(p.relative_to(R)):sha(p) for p in sorted(R.rglob('*')) if p.is_file() and p.suffix in allowed and p.name!='frozen-manifest.json' and '__pycache__' not in p.parts}
 m={'frozen_utc':datetime.now(timezone.utc).isoformat(),'scope':'Independent C8 statement, copied-source, axiom, kernel, negative-control and preservation review. Accepted finite supplied-input scalar contract only.','excluded':'Compiled Lean products and Python caches; abandoned diagnostic plans remain explicitly labeled.','files':files}
 (R/'frozen-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
 assert all(sha(R/f)==h for f,h in files.items())
 print(json.dumps({'accepted':True,'bindings':len(files),'manifest_sha256':sha(R/'frozen-manifest.json'),'verification_sha256':sha(R/'verification.json'),'report_sha256':sha(R/'REPORT.txt')}))
if __name__=='__main__':main()
