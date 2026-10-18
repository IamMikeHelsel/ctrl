#!/usr/bin/env python3
"""Bind accepted proof, frozen data, manuscript claims and reproducible review evidence."""
from pathlib import Path
import hashlib,json,time
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5]
BUILDER=HERE.parent/'builder';BIND=HERE.parent/'bindings';ROBOT=HERE.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
reports={n:json.loads((HERE/(n+'.json')).read_text()) for n in
 ('proof-review','integration-review','coverage-review','global-review','binding-audit')}
assert all(d['passed'] for d in reports.values())
base=reports['proof-review'];integ=reports['integration-review']
for m,p in base['source_paths'].items():assert sha(WORK/p)==base['source_hashes'][m]
for m,h in integ['source_hashes'].items():assert sha(BIND/(m+'.lean'))==h
assert sha(BUILDER/'NativeCoverage.lean')==reports['coverage-review']['coverage_source_sha256']
assert sha(BUILDER/'NativeGlobal.lean')==reports['global-review']['global_source_sha256']
assert all(sha(Path(p))==h for p,h in reports['binding-audit']['source_hashes'].items())
freeze_paths={
 BUILDER/'source-freeze.json':'1a3a8e44d81c29701cf89efa6e18af4fa4c3ea79c7ae1380ddfe88cd3e7b9399',
 BIND/'source-freeze.json':'afbd2f364063e4cc54d1b823ef1dac9705bd3932a4155ecb490669935c9f1dea',
 BUILDER/'coverage-source-freeze.json':'048ce28b392571e8e9bb56bf840c10b537284f61986b3aa7e2f8271126dc886c',
 BUILDER/'global-source-freeze.json':'e33f00f47d70c3ed0af55f9bb68b135e3c998f5e8c448228a830f1dfc8a3bbf1'}
for p,h in freeze_paths.items():assert sha(p)==h
frozen={}
expected={
 'native-execution-06/builder':'aaae586029babf2e9381d09ff34fb7b488495630c48abde27ab9b4d8ece1a803',
 'native-execution-06/grader':'abfb2e4527200fafafe6e93b57415920240796dc7497bc8e95c95ac25b4084bf',
 'latency-noise-05/builder':'8266eb7bd4da50d20f8fce651100126df1c9876b223c94a28d67c610fa3f4f78',
 'latency-noise-05/grader':'3c1c1d16f17e40ba92e9f240031040ea03dc45dda1a881cc03f3ff62d8fde45d'}
for rel,h in expected.items():
 folder=ROBOT/rel;manifest=folder/'artifact-sha256.json';assert sha(manifest)==h
 files=json.loads(manifest.read_text())['files']
 for n,want in files.items():
  want=want['sha256'] if isinstance(want,dict) else want
  assert sha(folder/n)==want,(rel,n)
 frozen[rel]={'manifest_sha256':h,'unchanged_files':len(files)}
(HERE/'preservation-review.json').write_text(json.dumps({'passed':True,'prior_frozen_artifacts':frozen,
 'current_source_freezes':{str(p.relative_to(WORK)):h for p,h in freeze_paths.items()},
 'all_reviewed_source_hashes_unchanged':True},indent=2)+'\n')
paper=WORK/'publication/robot-motion/execution-note/rounded-handoffs.tex'
text=paper.read_text()
for phrase in ('Let $\\sigma>0$','with $d_k\\geq0$','local segment jerk bound',
 'The JSON-to-Lean parser is not kernel-verified.','0.128125000188',
 'All earlier true-goal failures remain.','global classical third derivative'):
 assert phrase in text,phrase
paperreview={'decision':'accept within reviewed scope','source':str(paper.relative_to(WORK)),
 'source_sha256':sha(paper),'reviewed_scope':'Whole rounded-handoffs.tex section; mathematical/data/validation claims only. Not whole paper novelty, references, PDF layout or publication acceptance.',
 'explicit_assumptions':'positive sigma, nonnegative durations, per-piece physical dynamics and rate/disturbance bounds, local jerk bound, exact actual-state joins, initial cube, transformed reference-jump reserve',
 'qualifications':'Independent export-to-Lean value binding; parser not kernel-verified. Reference-relative result, not true-goal success, firmware proof, physical rest, or exact global jerk/acceleration limit.'}
(HERE/'manuscript-claim-review.json').write_text(json.dumps(paperreview,indent=2)+'\n')
kernel=[]
for n in ('proof-review','integration-review','coverage-review','global-review'):
 for step in reports[n]['steps']:
  if 'kernel' in step['label']:kernel.append(step['label'])
assert len(kernel)==13 and len(reports['global-review']['axioms'])==630
grade={'decision':'accept','milestone_grade':'A',
 'grade_scope':'Bounded exact exported-polynomial conditional tracking bridge. Not novelty or publication odds.',
 'native_schedules':12,'exact_cubic_pieces':886,'joins':874,
 'position_bound_m':'41/320000 + 188/1000000000000000',
 'position_bound_mm':'0.128125000188',
 'source_faithful_scope':'Exact rational interpretation of frozen06 exported binary coefficients and clocks.',
 'fresh_local_modules_including_controls':46,'inherited_public_statements':554,
 'new_core_statements':{'RoundedHandoff':14,'NativeData':12,'NativeBridge':13,
 'NativeInstances':13,'NativeCoverage':5,'NativeGlobal':1},
 'new_core_statements_total':58,'builder_witness_statements':9,'reviewer_witness_statements':9,
 'full_public_axiom_count':630,'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'separate_kernel_replays':kernel,'false_acceptance_attempts_rejected':5,
 'additional_negative_property':'Dropping the initial native interval is kernel-proved to fail the checker.',
 'actual_state_reset':'None permitted; exact position/velocity/acceleration matching is an explicit premise.',
 'segment_propagation':'Derived from IsTrajectory and physicalInput through tracking_cube_scaled, not assumed as a tracking-bound premise.',
 'absolute_time':'Every real time in the checked horizon has a valid recorded piece and local offset with the position-error bound. Both piece endpoints are included.',
 'not_claimed':['native solver correctness','floating-point at_time fidelity at all real times','firmware or hardware acceptance',
 'a global classical reference jerk bound','exact nominal velocity or acceleration limits','physical stopping',
 'true-goal task success','trajectory existence for all supplied coefficient functions','a new general hybrid-systems principle'],
 'next_useful_test':'A true-goal certificate must combine reference-to-goal error with the tracking allowance, or use a tighter validated physical trajectory bound. The existing near-limit numerical hold passes are not made formal by this internal bound.',
 'stop_condition':'This bounded bridge is closed. Freeze the evidence; no new parameter runs or tuning are needed for this gate.',
 'manuscript_source_sha256':sha(paper),'finished_utc':datetime.now(timezone.utc).isoformat()}
(HERE/'grade.json').write_text(json.dumps(grade,indent=2)+'\n')
report='''ACCEPT — Grade A for the bounded proof milestone.

The reference-rounding bridge is closed for the exact polynomial interpretation
of the12 frozen06 native schedules. The bound is0.128125000188 mm relative to
the exported reference, under the explicit physical assumptions. This grade is
about the checked milestone. It is not a publication or novelty grade.

The new finite induction uses actual plant trajectories and the existing
tracking theorem. It does not assume the desired segment bound. Exact physical
state matching gives transformed_error_after = transformed_error_before minus
transformed_reference_jump. A proved triangle bound adds each join reserve once.
The invariant cube remains valid at the larger radius. No global C2 reference,
switch derivative, hidden reference speed/acceleration limit, or trace reset is
used. Separate absolute-state bounds require separate reference bounds.

An independent rational audit checked all886 pieces and874 joins, including
every exact binary coefficient and clock endpoint. It also parsed every Lean
literal directly against frozen06. The Lean checker, rational-to-real bridge,
and12 named position certificates compiled. Coverage and its final composition
prove that every real time in the checked horizon has a valid local piece and
the same position-error bound. Reference jumps may give different left/right
reference values at a switch. The local theorem includes both sides; it does not
assert a global classical third derivative there.

The review independently compiled46 local modules, including witness controls,
against the pinned Lean4.35.0 and Mathlib dependency cache. It did not import
builder-produced local objects. The full630-statement audit used only propext,
Classical.choice and Quot.sound. There are554 inherited statements,58 new core
statements,9 builder witnesses and9 reviewer witnesses. The58 include generic
lemmas,12 data checks and12 named instances; they are not58 research discoveries.
Thirteen distinct modules passed separate Lean kernel replay.

Five false acceptance attempts were rejected: omitted jump reserve, resetting
the radius instead of adding it, omitted physical matching, an altered native
position coefficient, and an enlarged unchecked horizon. The reviewer also
proved rejection after dropping the first native interval. These failures were
mathematical rejections, not missing imports or parser failures. Positive witness
proofs show why position-only joins miss velocity and acceleration changes.

The argument is a useful verified application of a standard additive jump-bound
principle. It repairs a real mismatch with the former exact-join theorem. It does
not prove native solver or firmware correctness, close all native arithmetic
rounding errors, prove real robot behavior, or establish new task success. The
JSON-to-Lean conversion remains an independently audited binding, not a verified
parser. The06 numerical and finite native-fidelity evidence retain their original
scope. Gate05 remains failed. Exact exported nominal acceleration excess and
jump-sensitive command variation remain visible and unchanged.

All source freezes and all listed05/06 builder/grader artifacts were rehashed.
No frozen source changed. The corrected rounded-handoffs.tex section was checked
and its source hash is recorded in manuscript-claim-review.json. This is a scoped
claim review, not a review of the entire paper or its layout.

Next: connect an authoritative task goal to the admitted reference, then prove
the reference-to-goal margin plus physical tracking allowance meets the task
limit. The0.128125000188 mm internal bound alone cannot make every near-limit
numerical hold pass formal. Do not retune or rerun this gate. Preserve it and stop.

Reproduce in order with local Python: binding_audit.py; proof_review.py
RoundedHandoff HandoffWitnesses ReviewWitnesses; integration_review.py NativeData
NativeBridge NativeInstances; coverage_review.py; global_review.py. Scripts only
write this grader directory. Build objects are disposable and are removed after
the final checks; source copies, object hashes, logs and all reports are retained.
'''
(HERE/'review-report.txt').write_text(report)
# Keep copied Lean sources and negative witnesses; remove only this review's build cache.
removed=0
for p in (HERE/'build').rglob('*'):
 if p.is_file() and p.suffix!='.lean':p.unlink();removed+=1
(HERE/'cache-cleanup.json').write_text(json.dumps({'removed_own_build_cache_files':removed,
 'copied_lean_sources_retained':True,'cache_hashes_retained_in_review_reports':True},indent=2)+'\n')
files={str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*')) if p.is_file() and p.name!='artifact-sha256.json' and '__pycache__' not in p.parts}
manifest={'frozen_utc':datetime.now(timezone.utc).isoformat(),'decision':'accept','milestone_grade':'A',
 'file_count':len(files),'total_file_bytes':sum((HERE/n).stat().st_size for n in files),
 'source_freezes':{str(p.relative_to(WORK)):h for p,h in freeze_paths.items()},'files':files}
(HERE/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'passed':True,'files':manifest['file_count'],'bytes':manifest['total_file_bytes'],
 'manifest_sha256':sha(HERE/'artifact-sha256.json'),'manuscript_source_sha256':sha(paper),
 'frozen_utc':manifest['frozen_utc']},indent=2))
