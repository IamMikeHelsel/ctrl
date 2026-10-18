from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    v=json.loads((HERE/'verification.json').read_text())
    assert v['status']=='PASS'
    assert len(v['builds'])==15 and len(v['kernel'])==15 and len(v['negative_controls'])==6
    assert v['source_preservation']=='PASS'
    cases=json.loads((HERE/'oracle-cases.json').read_text())['cases']
    report=f'''VELOCITY ADMISSION — builder milestone 04
Finished {v['finished_at_utc']}
Status: builder verification passed; independent acceptance is still required.

Result
The new sufficient rational checker proves an all-future real reference speed
bound. It derives each cubic cell from the existing retained FIR reference.
It checks the four Bernstein coefficients formed from endpoint velocity and
acceleration. Current time and the final zero-speed tail are included.
Repeated, unsorted, queued and expired events require no extra assumptions.
Positive filter width and nonnegative speed bound are explicit requirements.

The checker is composed with the existing finite A/J/deadline selector. A
selected candidate preserves the issued reference prefix, satisfies all three
reference derivative bounds, and reaches reference rest by the deadline.
The old checker interfaces and frozen sources were not changed.

Nonvacuity
With h=0.2 s, V=1/15 m/s, A=0.5 m/s^2, J=7.5 m/s^3 and D=1.7 s, the unchanged
two-candidate list selects the return at 0.62 s. It retains the first event
at 0.22 s and the 20 mm signed increments. The same list returns none under
the 1.3 s deadline. The main theorem does not assume the desired speed bound.

Two distinct failure controls
1. Endpoints do not suffice. With h=1 and events (0,1),(1,-1), every future
   event knot has speed <=1/2, but v(9/5)=409/750>1/2. The new test rejects it.
2. The new test is conservative. With events (0,1),(1/4,-1), it rejects V=1/6.
   Adding the zero-size events (1/2,0),(3/4,0) changes no velocity but refines
   its cells. This version passes. Lean transfers its all-future bound to
   the original history. The rejected history is therefore proved safe.
   The independent Fraction polynomial calculation gives coefficient maxima
   3/16 for the original partition and 1/6 after refinement.

These examples distinguish an actual violation from a rejected sufficient
certificate. `none` means all supplied finite checks rejected. It does not
prove that every listed candidate is unsafe or that no feasible motion exists.

Verification
All {len(v['builds'])} local modules were rebuilt from fresh copied sources. The project
build cache was excluded; the pinned dependency caches were reused. All
{len(v['kernel'])} modules then passed separate leanchecker replay. The axiom audit covered
{v['audited_declarations']} local declarations, including generated proof declarations, and allowed
only propext, Classical.choice and Quot.sound. No local axiom, unsafe proof,
sorryAx or native_decide was accepted. These counts are audit coverage.

An exact Fraction generator forms ordinary cubic powers on sorted knot cells
and converts them to Bernstein coefficients. It does not import a Lean
checker implementation. Its {len(cases)} decisions on 60 histories ({sum(x['expected'] for x in cases)} acceptances and
{sum(not x['expected'] for x in cases)} rejections) all compile with decide +kernel and passed kernel replay.
Six intentionally false claims failed for mathematical reasons. Import and
identifier failures do not count. The logs retain the actual errors.

The source freeze predates final verification. All source hashes and prior
source/pin bindings were checked before and after. Three failed development
versions remain in attempts/. Those failures were Bool rewriting, cast and
negation-normalization errors; none is used as accepted evidence.

Important boundaries
The bound is on the concrete scalar reference. It is not a physical actuator
or Franka speed bound, travel-clearance proof, sampled-loop guarantee, force,
torque, saturation or hardware result. It covers a finite retained event list,
not an infinite stream of accepted replans. The velocity guard is sufficient,
not exact or complete. No subdivision optimization is provided.

The combined checker still calls the old all-pairs acceleration checker.
The successor optimization supplies the adjacency operation but its timing
results are not transferred to this combined checker. No runtime, memory or
real-time cost claim is made. This gate is a checked contract; it does not
claim that Bernstein bounds or FIR planning are new.

Next gate
An independent critic should read the cubic identity and Boolean-to-real
bridge, replay the fresh closure, and challenge the conservative rejection
and endpoint-only witness. If accepted, root can add this contract to the
focused paper and portable reviewer bundle. Further proof expansion is not
needed for this milestone. A stronger optimizer/baseline is a separate test.

Evidence files
CLAIMS.txt and DERIVATION.txt give the exact statement and plain explanation.
verification.json records all commands, statuses and log hashes.
source-closure.json, source-freeze.json and input-bindings.json bind sources.
reproduction.txt explains a fresh sibling-folder replay.
Source-freeze SHA256: {sha(HERE/'source-freeze.json')}
'''
    (HERE/'report.txt').write_text(report)
    files={str(p.relative_to(HERE)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(HERE.rglob('*'))
       if p.is_file() and '.cache' not in p.parts and '__pycache__' not in p.parts and p.name!='artifact-sha256.json'}
    manifest={'created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'status':'builder verified; independent review pending','exclusions':['.cache/**','__pycache__/**'], 'files':files}
    (HERE/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'manifest_sha256':sha(HERE/'artifact-sha256.json'),'files':len(files),'status':v['status']}))
if __name__=='__main__':main()
