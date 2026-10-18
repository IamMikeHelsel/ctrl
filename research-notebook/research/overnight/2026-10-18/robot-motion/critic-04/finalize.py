from pathlib import Path
import datetime,hashlib,json
H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((H/'final-result.json').read_text())
first=json.loads((H/'result.json').read_text())
o=json.loads((H/'oracle-result.json').read_text())
assert r['status']=='PASS'
assert first['status']=='FAIL' and first['commands'][-1]['label']=='build-ReviewerWitnesses'
assert all(x['exit_code']==0 for x in first['commands'][:-1])
assert len([x for x in r['commands'] if x['label'].startswith('kernel-')])==17
neg=[x for x in r['commands'] if x['label'].startswith('negative-')]
assert len(neg)==8 and all(x['exit_code']!=0 for x in neg)
for name in ['ReviewerOracle.lean','ReviewerWitnesses.lean','EnvironmentAudit.lean']:
    assert sha(H/name)==sha(H/'.cache/fresh'/name),name
for p in (H/'negative-controls').glob('*.lean'):
    assert sha(p)==sha(H/'.cache/fresh'/p.name),p.name
report=f'''INDEPENDENT REVIEW — velocity admission, milestone 04
Decision: ACCEPT the bounded scalar reference contract.
Finished: {r['finished_utc']}

The four-coefficient sufficient speed check is connected to the actual retained
FIR reference. The proof covers every future real time, current time, event
knots, strictly adjacent cells and the final zero-speed tail. Positive filter
width and nonnegative bound are enforced by the test. Repeated, unsorted,
queued, expired and signed events need no extra hidden assumptions.

The selected candidate preserves the old reference through its execution time,
satisfies reference V/A/J bounds, and reaches reference rest by the deadline.
The unchanged two-time example selects 0.62 s at V=1/15 m/s, A=0.5 m/s²,
J=7.5 m/s³ and D=1.7 s. It returns none for D=1.3 s. The caller still owns
the link between final reference position and an external task goal.
The independent oracle checks that its reference is moving at current time
0.52 s: velocity is 23/480 m/s and acceleration is 5/16 m/s².

Crucial rejection distinction
The endpoint-only example has a real interior violation: 409/750 > 1/2 at
t=9/5. By contrast, the conservative example is proved safe at V=1/6 although
its unrefined Bernstein coefficients reach 3/16. Zero-size events refine the
cells and certify the unchanged velocity. Thus none means all supplied finite
tests rejected, not that the listed motions are unsafe or that no feasible
motion exists. The partition depends on the event representation.

The zero-event refinement is not a proved rewrite of the whole timed selector.
Its deadline test also counts zero-size event tails. Use a separate certificate
partition if subdivision is automated later. Do not silently transfer earlier
acceleration/jerk pruning equivalence or successor timing to this new guard.

Independent evidence
- Rebuilt all 15 frozen local modules from copied fresh sources. The project
  build cache was excluded. Pinned external package and Lean library caches
  were reused. No toolchain or source pins changed.
- Rebuilt the reviewer oracle and 15 theorem clients. The clients exercise
  generic soundness, real reference rest, prefix preservation, cancellation,
  strict successor behavior, invalid input, safe rejection and true violation.
- Separate leanchecker replay passed for all 17 modules.
- The axiom audit covered {r['audited_declarations']} local declarations, including all
  {r['builder_local_declarations']} builder-local declarations and generated proof declarations.
  Only propext, Classical.choice and Quot.sound were allowed. No local axiom,
  unsafe declaration or sorry/native-decide dependency was accepted.
- An independent Fraction oracle used cardinal B-spline degree recursion,
  not the builder's positive-part powers or checker code. It checked
  {o['decisions']} decisions ({o['accepted']} acceptances, {o['rejected']} rejections) on {o['histories']} histories,
  {o['jet_pairs']} exact velocity/acceleration pairs and {o['cell_identity_checks']} interior cell identities.
  All generated Lean decisions/equalities passed, then passed leanchecker.
  These finite cases supplement the universal proof; they do not replace it.
- Eight false claims failed at explicit False goals. Import, name and tactic
  progress errors were excluded. Both original (85 files) and corrected
  builder (92 files) manifests, source freeze, closure and pins were preserved.

Preserved failures
The builder's original negative harness accepted a tactic-progress failure.
Its correction is explicit, and the first failure remains preserved. This
review does not rely on that initial six-control claim. Our first environment
preflight omitted the pinned Lean standard-library path. Our three real-time
client conversions then needed neg_div normalization. Both reviewer failures
are preserved. The first run result remains FAIL; final-result.json records
the repaired client, complete audit, all kernel replays and strict negatives.
No builder theorem changed during this review.

Done/open boundary
Accepted: sufficient all-future reference velocity admission and its finite
V/A/J/reference-rest-deadline composition. This is a bounded proof gate.
Open: actual actuator velocity at the same bound; physical speed/acceleration
settling by the numerical task deadline; coupled arms, travel clearance,
sampling/latency, saturation, force/torque, hardware, infinite replanning,
optimality, real-time cost, novelty and publication readiness. In particular,
reference rest is not a proof that a physical robot is at rest.

Next productive gate
Integrate the accepted contract into the focused paper and a separately reviewed
portable bundle. Keep the conservative rejection example visible. Stronger
common-state smooth-return comparisons are more useful next than adding proof
counts. A physical terminal claim requires a declared controller/model bridge.

Input final manifest SHA256:
025661f2f14bd9bdb3ef12ba49bdbd73d364c41971da1e749c50073a07e46023
Input source-freeze SHA256:
c55250cfe0744adcdc30e4ea9434b41c1052b1ba4cd2dd49271fb89a15be0eae
Read SCOPE-REVIEW.txt, reproduction.txt, result.json and final-result.json.
'''
(H/'report.txt').write_text(report)
files={str(p.relative_to(H)):{'sha256':sha(p),'bytes':p.stat().st_size}
       for p in sorted(H.rglob('*')) if p.is_file() and '.cache' not in p.parts
       and '__pycache__' not in p.parts and p.name!='artifact-sha256.json'}
manifest={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'decision':'ACCEPT bounded scalar reference contract; no physical or novelty acceptance',
          'files':files,'exclusions':['.cache/**','__pycache__/**']}
(H/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'manifest_sha256':sha(H/'artifact-sha256.json'),'files':len(files),'status':'ACCEPT'},indent=2))
