from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;P=R/'package-v4';F=R/'fresh-replay-v4'
proof=json.loads((F/'results.json').read_text());assert proof['passed'] and proof['local_modules']==63 and proof['audited_declarations']==3944 and proof['kernel_replays']==22 and proof['negative_controls_rejected']==33
clients=json.loads((R/'client-results-v4.json').read_text());assert len(clients)==29 and all(t['passed'] for t in clients)
failures=json.loads((R/'object-failure-results-v4.json').read_text());assert len(failures['tests'])==6 and all(t['passed'] for t in failures['tests'])
race=json.loads((R/'output-snapshot-race-v4/finding.json').read_text());assert race['passed'] and race['no_success_result']
neg=[]
for step in proof['steps']:
 if not step['label'].startswith('negative-'):continue
 t=(F/'logs'/(step['label']+'.log')).read_text();assert 'unsolved goals' in t and '⊢ False' in t,step['label'];assert not any(x in t for x in ['unknown identifier','unknown constant','unknown module','object file','failed to synthesize','type mismatch']),step['label']
 neg.append({'label':step['label'],'exit_code':step['exit_code'],'explicit_false_goal':True})
assert len(neg)==33
(R/'negative-log-review-v4.json').write_text(json.dumps(neg,indent=2)+'\n');(R/'EnvironmentAudit-V4.lean').write_bytes((F/'.build/EnvironmentAudit.lean').read_bytes())
summary={'decision':'ACCEPT V4 within its stated offline proof and local provenance scope.','artifact_gate':'PASS','package_manifest_sha256':'73f004177733a1384a2bb7f22417d910c9da6b359088159c8d58f46ab13b23ed','package_files_verified':153,'fresh_modules':63,'audited_declarations':3944,'kernel_replays':22,'mathematical_false_clients_rejected':33,'valid_json_proof_clients':10,'valid_json_accepted':4,'valid_json_rejected':6,'malformed_json_clients_rejected':19,'ordinary_object_record_failures_rejected':4,'injected_missing_proof_check_failures_rejected':2,'external_input_path_race_passed':True,'saved_snapshot_race_rejected_before_success':True,'damage_tests':{'count':8,'run_version':'V3','V4_replay_and_plans_byte_identical':True},'hardware_test':False,'publication_novelty_review':False,'external_human_peer_review':False,'shared_source_or_pin_files_changed':False}
(R/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
(R/'REPORT.txt').write_text('''Independent final package review — 18 October 2026 UTC

Decision
ACCEPT version 4 as a portable offline proof package and rational-input proof
client, within the stated local trust and model limits. Artifact reproducibility
and provenance gate: PASS. No Lean theorem source repair was needed. This does
not establish publication novelty, external human peer review, a live robot
result or a real-time implementation.

Reviewed artifact
publication/robot-motion/overnight-reviewer-bundle-v4/artifact-sha256.json
SHA256: 73f004177733a1384a2bb7f22417d910c9da6b359088159c8d58f46ab13b23ed
All 153 named files match. The reviewer used a separate copied package and a
new build directory. All original source and review bindings were checked.
Proof plans, local sources, parser, examples and replay code are byte-identical
to V3. V4 changes the saved-input check and input digest in the client, with
corresponding documentation and package metadata. Exact deltas are preserved.

Fresh proof evidence
All 63 local modules compiled from their copied sources. The declaration audit
checked all 3,944 local declarations; only propext, Classical.choice and Quot.sound
occurred. No unsafe local declaration or local axiom was accepted. All 22 named
separate kernel replays passed. All 33 mathematical false clients failed at an
explicit False goal. I inspected the final logs: missing imports, unknown names,
type errors and missing instances were not counted as negative proof evidence.
These counts measure audit coverage, not new mathematical contributions.

Local project build products were excluded. Fresh products came first on
LEAN_PATH; provisioned public dependency caches were reused. Lean 4.35.0 compiler
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc and mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679 were retained. Compiler, checker and public
library binaries remain trust boundaries. This is a fresh local-source replay,
not a from-source bootstrap of the full dependency ecosystem.

Two concrete wrapper repairs
V2 preflight accepted a changed lakefile.toml when the packaged and supplied
copies matched and the local input manifest was rehashed. V3 fixed all three
canonical dependency-file hashes. Eight damage tests then rejected source edits,
changed roots, an empty kernel plan, a removed negative control, and changes to
the dependency files. These tests ran against V3. The exact replay code and proof
plans are unchanged in V4, and their byte identity was checked independently.

V3 fixed the old external input-path race but could still record the wrong input
hash if its newly written output/input.json was edited during proof execution.
The real Lean proof remained for the original zero goal while result.json hashed
a changed 1/200 m goal snapshot. That counterexample is preserved. V4 now derives
the result digest from the raw bytes it parsed and rejects a changed saved
snapshot before success. The identical output-snapshot edit now ends with the
intended error and no success result.json. Its generated proof remains for the
original input. This is a local provenance repair, not tamper-proof attestation.

Final JSON-client evidence
Ten valid JSON runs compiled actual decision/consequence proofs and passed
separate kernel replay. They cover the six supplied examples, equality at the
execution clock boundary, rejection of negative dispatch, exact rational
normalization, and concurrent replacement of the external input path. Four
accept; six reject. Acceptance yields the reference contract. Rejection proves
that the live base is retained, not that the new task has been completed.

Nineteen malformed inputs reject: duplicate keys at two depths, invalid rational
values, code-like text, invalid versions, wrong fields, malformed event data and
the file-size limit. Parsing itself is not formally verified.

For the external input-path race, the original path was replaced after the probe
file appeared. The output snapshot and result digest still matched the original
proved bytes; the generated Lean literals did too. The saved-output-snapshot
race described above was a separate test and now correctly fails closed.

Changed or missing proof objects, an incomplete replay record and a missing
object record all reject. Original object and record bytes were restored and
rechecked. Two reviewer-injected failures also reject: a nonzero kernel step and
a missing theorem-axiom audit log. Those injections test failure handling; they
are not additional mathematical proof replays. No failed final client run
produced a success result.json.

Actual guarantees and limits
I read the FutureCommit, velocity and FIRHold theorem statements. Successful
commit binds the reference proof to full live history and task equality, exact
signed goal increment, finite candidate selection and supplied ideal timestamps.
The earlier reference is unchanged through execution. Reference V/A/J bounds hold
from request time; exact reference rest holds from the absolute deadline. The
speed check is sufficient and can reject safe motion. The finite candidate list
can miss feasible choices. Later commits may supersede a task. Rejection may
leave the old goal active. No liveness or computation-capacity theorem follows.

The physical result applies to the fixed scalar controller and a supplied
classical trajectory, with bounded response/disturbance and one initial error
cube. The same physical state and clock-shifted inputs pass into the final hold.
It gives residual bands, not exact physical rest. The speed/acceleration terminal
time is 3.42 s, not the numerical task deadline of 1.70 s. No coupled Franka,
obstacle, machine-safety or hardware result follows from this scalar theorem.

Truthful measured timing, common clocks, atomic live-state capture/update, the
parser, runtime and completed local replay record are trusted interfaces. The
fresh output directory is locally owned evidence. Hashes are not signatures and
do not prevent someone with control of all scripts, records and outputs from
replacing them. No hostile-machine or authenticated-attestation claim is made.
The numerical comparison and offline optimizer remain separate evidence.

Preserved work and stop decision
V2's pin fault, V3's snapshot counterexample, the partial stopped V2 replay, the
complete V3 replay and all test logs remain available. The first reviewer mutation
harness used a wrong workspace-parent index; its failures are retained under
attempt-01 and were not counted as passing tests. Temporary read-only cache links
were removed after recording their targets; shared dependencies were untouched.
REPRODUCE.txt and the saved scripts give exact commands. No shared source, paper,
state, Git checkout, hardware or external service was changed by this reviewer.
Stop this review branch at the accepted V4 gate. Remaining publication and robot
questions belong to their separate assessments.
''')
print(json.dumps(summary,indent=2))
