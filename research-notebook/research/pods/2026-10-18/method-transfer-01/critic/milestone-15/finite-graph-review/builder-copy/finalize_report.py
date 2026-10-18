#!/usr/bin/env python3
"""Write final E9 report/index only after a complete fresh verification passed."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys
HERE=Path(__file__).resolve().parent
fresh=HERE/sys.argv[1]
v=json.loads((fresh/'verification.json').read_text())
assert v['passed'] and v['source_hashes_stable']
assert len(v['axioms'])==102 and len(v['negative_controls'])==4
assert all(set(a)<=set(v['allowed_axioms']) for a in v['axioms'].values())
assert len(v['runs'])==30
for run in v['runs']:
 assert run['exit']==(1 if run['label'].startswith('reject-') else 0),run
p=json.loads((HERE/'INPUTS.json').read_text())
assert p['prior_files_verified']==317
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
index={'created_utc':datetime.now(timezone.utc).isoformat(),
 'scope':'Actual finite-graph fractional-half bridge from rational completed-square certificates; pending independent acceptance',
 'main_endpoint':'Erdos128.FiniteProfileBridge.half_from_squared_certificates',
 'main_source':'FiniteGraphBridge.lean','arithmetic_source':'SquareCertificate.lean','control_source':'FiniteControls.lean',
 'helper_extraction':'CutHelpers.lean','exact_statement':'EXACT-STATEMENT.txt',
 'verification':str((fresh/'verification.json').relative_to(HERE)),
 'verification_sha256':sha(fresh/'verification.json'),
 'unchanged_upstream_modules_built':7,'unchanged_accepted_E8_modules':1,'extracted_ported_helper_modules':1,
 'new_E9_modules':3,'fresh_compilation_modules':13,'public_theorems_audited':102,
 'separate_kernel_checks':13,'expected_mathematical_rejections':4,'allowed_axioms':v['allowed_axioms'],
 'all_checks_passed':True,'independent_acceptance':False,'full_point0251_endpoint':False,
 'replay_entry':'replay.py','prior_packets_intact':9,'prior_files_intact':317,
 'source_notes':'SOURCE-NOTES.txt','retained_failures':'FAILURES.txt','remaining_work':'REMAINING.txt'}
(HERE/'FINAL-INDEX.json').write_text(json.dumps(index,indent=2)+'\n')
(HERE/'REPORT.txt').write_text(f"""E9 FINITE-GRAPH FRACTIONAL-HALF BRIDGE
18 October 2026. Builder packet; independent acceptance pending.

The requested bridge is implemented. For an actual nonempty finite triangle-
free graph and its supplied oriented cut, rational R,L with R>=0, strict
larger-side mass y>1/2 and the two completed-square tests imply an actual
ambient fractional half with normalized edge cost at most R. The source
proves square transport, induced-side normalization and zero extension.
It adds no global-density or maximum-cut assumption. The cut structure's
BCL budget remains explicit; the construction does not use that number.

The endpoint is half_from_squared_certificates in FiniteGraphBridge.lean.
SquareCertificate.lean gives the exact rational identities. CutHelpers.lean
is an attributed selected extraction and compatibility port, with complete
original bytes, source ranges and patch. Seven upstream modules and the
accepted E8 source remain unchanged. See EXACT-STATEMENT.txt and SOURCE-NOTES.

The actual six-vertex example has one edge. Its constant large-side profile
has local objective 9/625, ambient mass 3 and normalized cost 1/100. The
square tests are -1/5850 and -19/22500. The same graph also has an independent
half with cost zero; this is no sharpness claim. Exact semantic controls
reject cost scaling by y, local mass 1/2, an unscaled slope and the balanced
alpha<1 assertion. See CONTROLS.txt and the compiled FiniteControls source.

Verification completed at {v['completed_utc']}:
  {str((fresh/'verification.json').relative_to(HERE))}
All 13 fresh compilations, all 102 public theorem axiom audits, all 13
separate leanchecker runs and four expected mathematical rejections passed.
Only propext, Classical.choice and Quot.sound occur in the audited closures.
The rejection logs contain mathematical unsolved goals, not setup errors.
The replay imports no development or prior research build products. It uses
the existing pinned Lean4.35/mathlib dependency cache; this is not a full
mathlib source rebuild or a replay under the upstream Lean4.30 pin.

All 317 files in nine prior builder freezes match their hashes. Thirteen
failed development attempts are preserved; no statement was weakened to
repair them. They are separate from the successful fresh evidence.

This closes the assigned conditional finite-graph construction. It does not
establish the full .0251 endpoint. The 872-cell cover, old branch composition,
BCL all-order transfer, blowup and floor-half rounding remain later steps.
No constant optimization or novelty claim was made. Root owns repository
sync, commits and pushes; the builder performed none of those operations.

Replay from a separate copy inside this workspace:
  python3 replay.py
It creates a fresh evidence directory and uses the recorded local toolchain
and package cache. Do not run provenance.py or finalize_report.py in the
frozen packet, since those scripts write metadata. Independent acceptance
belongs to the reviewer. Stop after freeze and await the next assigned gate.
""")
(HERE/'CLAIMS.txt').write_text("""E9 BUILDER CLAIMS — PENDING INDEPENDENT REVIEW

1. The Lean theorem constructs an actual ambient rational fractional half
   from the supplied finite triangle-free graph, oriented cut and explicit
   rational completed-square certificate. No feasible half, graph moment
   or graph objective bound is assumed.
2. The universal square identities, slope L/y, mass alpha=1/(2y), degree
   scaling, cost scaling y^2 and zero extension are proved. The balanced
   y=1/2 case is excluded before any positive-denominator argument.
3. The nonzero six-vertex profile and a distinct zero-cost independent half
   are proved. Four exact mathematical false alternatives are rejected.
4. Thirteen fresh builds, 102 public axiom closures, 13 separate kernel
   checks and four expected rejections passed. Standard axiom allowlist
   only; no new axiom, sorry, admit or unsafe proof shortcut was used.
5. Seven upstream modules and accepted E8 source are unchanged. Selected
   helper extraction and its compatibility edit are fully attributed and
   patched. Original and executed pins remain separate and unchanged.
6. No full .0251 Lean endpoint, integral-half theorem, universal BCL proof,
   new constant, sharpness or novelty claim is made. No self-acceptance.
""")
print(json.dumps(index,indent=2))
