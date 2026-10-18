from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parent;P=R/'package-v3';F=R/'fresh-replay-v3'
result=json.loads((F/'results.json').read_text());assert result['passed'] and result['local_modules']==63 and result['kernel_replays']==22 and result['negative_controls_rejected']==33
assert result['audited_declarations']==3944
clients=json.loads((R/'client-results.json').read_text()); assert len(clients)==29 and all(t['passed'] for t in clients)
failures=json.loads((R/'object-failure-results.json').read_text());assert len(failures['tests'])==6 and all(t['passed'] for t in failures['tests'])
mutants=json.loads((R/'mutation-results-v3.json').read_text());assert len(mutants)==6 and all(t['exit_code']!=0 for t in mutants)
assert all(x['passed'] for x in json.loads((R/'all-pin-mutations-v3.json').read_text()))
negative=[]
for step in result['steps']:
 if not step['label'].startswith('negative-'):continue
 text=(F/'logs'/(step['label']+'.log')).read_text()
 assert 'unsolved goals' in text and '⊢ False' in text,step['label']
 assert not any(x in text for x in ['unknown identifier','unknown constant','unknown module','object file','failed to synthesize','type mismatch']),step['label']
 negative.append({'label':step['label'],'exit_code':step['exit_code'],'all_errors': [s for s in text.splitlines() if 'error:' in s], 'explicit_false_goal':True})
(R/'negative-log-review-v3.json').write_text(json.dumps(negative,indent=2)+'\n')
(R/'EnvironmentAudit-V3.lean').write_bytes((F/'.build/EnvironmentAudit.lean').read_bytes())
summary={'decision':'REPAIR V3 saved-output snapshot provenance. Proofs and ordinary clients passed; no theorem change needed.','package_manifest_sha256':'1d8ff565bcb9afcc89b2f6ad363b60f81e7de8698d8de7834891932f40530dd7','package_files_verified':152,'fresh_modules':63,'audited_declarations':3944,'kernel_replays':22,'mathematical_false_clients_rejected':33,'valid_json_proof_clients':10,'malformed_json_clients_rejected':19,'ordinary_object_record_failures_rejected':4,'injected_missing_proof_check_failures_rejected':2,'damaged_package_cases_rejected':8,'proof_sources_unchanged_from_v2':True,'v2_replay_partial_not_acceptance':True,'input_path_race_snapshot_bound':True,'hardware_test':False,'publication_novelty_review':False,'external_human_peer_review':False}
(R/'result-v3.json').write_text(json.dumps(summary,indent=2)+'\n')

(R/'REPORT-V3.txt').write_text("""Independent final package review — 18 October 2026 UTC

Decision
REPAIR version 3 before final client acceptance. Its complete proof replay and
ordinary client tests pass. A later concrete output-snapshot edit can mislabel
the proved input hash. The minimal V4 repair is under separate review. Version 2
also required an exact dependency-file binding repair. No theorem repair is needed.
This decision does not establish publication novelty, external human peer review,
a live robot result or a real-time implementation.

Reviewed version
publication/robot-motion/overnight-reviewer-bundle-v3/artifact-sha256.json
SHA256: 1d8ff565bcb9afcc89b2f6ad363b60f81e7de8698d8de7834891932f40530dd7
All 152 frozen files match. The reviewer used a separate copied package and a
new build directory. All 63 theorem-source modules, the six component gates,
the proof plans, parser and client are unchanged from version 2. Only packaging
and dependency-file checks changed. Original component review manifests and
reports are bound by their fixed hashes. Old failures remain preserved.

Fresh proof evidence
All 63 local modules compiled from the copied sources. The declaration audit
checked all 3,944 local declarations; only propext, Classical.choice and Quot.sound
occurred. No unsafe local declaration or local axiom was accepted. All 22 named
separate kernel replays passed. All 33 mathematical false clients failed at an
explicit False goal. I inspected those logs; import, name, type and missing
instance failures were not counted as successful negative evidence.

The replay excludes project build caches and places its fresh local products
first on LEAN_PATH. It reuses provisioned public dependency caches. The compiler,
checker and library binaries remain trust boundaries. The pinned Lean version
is 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. The mathlib revision is
56a005855ea17e0b0958f73ec801ae140b0a1679.

Packaging fault found and fixed
The V2 precheck accepted a changed lakefile.toml when both the packaged file and
the supplied project's file had the same change and the local input manifest
was rehashed. That defeated the claimed exact three-file pin check, though it
changed no theorem. The V3 replay fixes the original hashes of lean-toolchain,
lakefile.toml and lake-manifest.json in its code. The old dual-copy mutation now
fails. Both other pin-file mutations also fail. Source edits, a removed source
root, an empty kernel plan and a removed negative client all fail despite local
input-manifest rehashing. Eight V3 damage tests reject in total.

JSON client evidence
Ten valid JSON runs compiled actual decision/consequence proofs and passed
separate kernel replay. They include the six supplied examples, equality at the
execution clock boundary, rejection of negative dispatch, exact rational
normalization, and the input-path replacement test. Four accept and six reject.
Acceptance yields the reference contract. Rejection proves that the live base
is retained; it does not certify the new task. Nineteen malformed inputs reject,
including duplicate keys at two depths, bad rational values, code-like text,
invalid versions, wrong fields, malformed event data and the file-size limit.

The original input path was replaced after ClientProbe.lean appeared. The changed
file asked for a different live goal. The real proof still covered the original
zero-goal input. The output input.json was byte-identical to that original input,
and result.json recorded its hash rather than the changed path's hash. Generated
Lean task literals also matched the original input. The old wrapper's reported
input-hash race is therefore repaired for this tested file-change scenario.

Ordinary changed or missing local proof objects, an incomplete replay record,
and a missing object record each reject. Exact original bytes were restored and
rechecked after those tests. Two reviewer-injected execution failures also reject:
a nonzero kernel step and a missing theorem-axiom audit log. These last two tests
exercise failure handling; they are not additional mathematical proof replays.
No ordinary failing client run produced a success result.json.

Additional output-snapshot counterexample
A controlled edit of the newly created output/input.json after ClientProbe.lean
appeared changed the stored live goal to 1/200 m. The compiled and kernel-checked
proof still used the original zero goal. V3 then recorded the changed snapshot
hash. This is narrower than hostile-machine attestation, but it defeats the
claimed direct binding between the result input hash and the parsed/proved bytes.
output-snapshot-race-v3/finding.json preserves the counterexample. The minimal
repair is to derive input_sha256 from the retained raw bytes and reject a changed
saved snapshot before success. This report therefore does not accept the final
V3 client. The ordinary external input-path race is repaired as stated above.

Claim boundaries
I read the actual FutureCommit, velocity and physical terminal theorem statements.
A reference guarantee does not automatically become a physical guarantee. The
future-commit theorem takes a common ideal clock and one atomic live-state
transition as premises. It proves neither timing capacity nor a progress rate.
Its finite list and sufficient speed test may reject feasible motions. Later
updates can supersede the task; rejection can leave the prior goal active.

The physical theorem concerns one scalar controller, a supplied classical
trajectory, bounded changing response/disturbance and one initial error cube.
It preserves the same physical state into the hold. It gives residual position,
speed and acceleration bands. Its terminal speed/acceleration time is 3.42 s,
not the numerical task's 1.70 s deadline, and it does not prove exact physical
rest. No coupled Franka, obstacle, machine-safety or hardware claim follows.

The parser, truthful measured timing, atomic implementation, runtime and completed
local replay record are trusted interfaces. The JSON record is not authenticated
remote attestation. Hashes do not prevent a person with control of scripts,
records and outputs from replacing all of them. The package makes no such claim.
The numerical comparison and offline optimizer are separate evidence and were
not converted into a Lean proof by this package review.

Preservation and stopping
The initial reviewer mutation harness had an incorrect workspace-parent index;
its errors are retained in attempt-01 and were not accepted as test results.
The partial independent V2 build was stopped when root requested the V3 repair.
All complete acceptance counts here refer to the fresh V3 replay. Temporary
read-only cache symlinks were removed after their exact targets were recorded;
shared dependency files were untouched. REPRODUCE.txt and the saved scripts give
the commands. No shared source, paper, state, Git checkout, hardware or external
service was changed. Continue only with the concrete V4 snapshot repair. Preserve this V3 evidence.
""")

print(json.dumps(summary,indent=2))
