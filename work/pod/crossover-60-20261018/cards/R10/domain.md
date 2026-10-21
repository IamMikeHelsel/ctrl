# R10 domain: complete admission needs more than a jerk gate

AI-written domain role; inherited root model, exact identifier unavailable. PM owns elapsed
time, acceptance, final rubric and continuation. Original sources and histories unchanged.

## Recovered source model and task

Read moving-goal-08/builder/{report.txt,README.txt,protocol.txt,packets.json,prepare.py,
make_references.py,knot_check.py,reference-extrema.json}. README identifies prepare.py and
run_batch.py as the active08 entry points; old standalone mains copied from06 must not run.
No original writer, physical batch or native planner was executed by this worker.

The four-box reference is q(t)=sum delta_i F((t-tau_i)/h), h=1/5, with
F(s)=sum_{j=0}^4 [1,-4,6,-4,1]_j*(s-j)_+^4/24. Initial reference and plant rest.
A revision appends delta=new authoritative goal minus previous ACCEPTED goal, never minus
current q or physical x. All previous signed events remain. Admission is ceil(ready/.02)*.02;
execution adds the fixed case buffer. Existing prefix, including queued execution, is immutable.

Source scenarios: initial +.02m goal ready.22; ordinary return0 ready.52, deadline1.70;
same return with deadline.51; buffered return ready.62 with .06 buffer on BOTH commands,
executions.28/.68 and deadline1.90; far return to-.02 ready.52, deadline1.90. All horizons2.5.
Reference limits are V=.1,A=.5,J=7.5. They are reference limits, not universal physical limits.

Plant x'=v,v'=a,a'=r(u+w-a), r80/100/120,w0/.01, with direct controller
u=q''-800(x-q)-60(v-q')-(a-q'')/2+j_q/96. No physical state reset at revisions.
Deadline demands actual |x-goal|<=.0002,|v|<=.001,|a|<=.02 and retention through2.5;
all proposals admitted, causal deadline after readiness/execution, referenceV/A/J, and
initial progress x(.50)-x(0)>=.001 are additional requirements. Rejection does not erase a
proposal or fulfill its task. Reference tail completion alone proves none of these physical
settling tolerances. Source18/24 native versus6/24 FIR remains prior sampled-model evidence.

## Independent exact reconstruction

`domain_fir.py` reads exact packets only, reconstructs derivatives with Fraction arithmetic,
and never imports producer helpers. On each interval between all shifted kernel knots,
position is quartic, velocity cubic, acceleration quadratic and jerk affine. Acceleration
extrema occur at endpoints or an interior zero of affine jerk; jerk extrema occur at endpoints.
Velocity is bounded by an exact cubic Bernstein certificate, a sufficient bound, not claimed
an exact velocity maximum. Candidate checks begin at admission, include queued events and
all retained signed history. Original jerk-only acceptance determines reproduced histories;
the new full gate is computed separately and does not rewrite the source's decisions.

Exact reproduced results:

| candidate revision | sufficient V upper | exact A peak | exact J peak | conclusion |
|---|---:|---:|---:|---|
| ordinary return |1/15|21/32 at t77/100|25/4|jerk admits, A fails|
| predelivery return |1/15|21/32|25/4|A fails and .51<.52 service failure|
| buffered return |1/15|1/2|5|full reference gate passes|
| far reversal candidate |2/15|71/72 at t349/450|45/4|A and J fail|

Far rejection retains accepted goal+.02 while authoritative goal is-.02. The40mm gap is
an actual task mismatch even when tracking the retained reference accurately. The velocity
bound2/15 is conservative and is not by itself a certified velocity violation.

A positive buffered reference certificate covers all seven complete-history knot intervals
and V/A/J:21 rational cubic Bernstein coefficient rows in domain_buffered_certificate.json.
Every coefficient meets its source nominal limit. Degree elevation covers quadratic/affine
pieces with the same cubic theorem. After last event+.8, reference derivatives vanish.
Coefficient reconstruction is exact Python evidence; it is not yet a kernel-verified compiler
from arbitrary event lists to interval partitions. The isolated Lean generic polynomial
lemma and independent reconstruction serve distinct evidence roles.

## Kernel witnesses and reusable bound

`domain_extrema.lean` compiled10 declarations with permitted axioms under ctrl Lean4.33.1.
On ordinary local piece t=.72+u:

    a(u)=-9/16-(15/4)u+(75/2)u²=(75/2)(u-1/20)²-21/32.

On the far-reversal candidate's corresponding piece:

    a(u)=-13/16-(25/4)u+(225/4)u²=(225/4)(u-1/18)²-71/72.

Exact witnesses certify the violations. A generic cubic Bernstein theorem proves an absolute
bound on every normalized u in[0,1] when its four coefficients meet that bound. These theorems
certify their stated polynomials; mapping finite event histories to those polynomials remains
explicit independent reconstruction, not silently claimed kernel refinement.

## A new retained-history delay policy candidate

Changing the policy is allowed only as a declared candidate, never as a rewrite of frozen08.
Keep old event(.22,+.02), h=.2, new target0 and deadline1.70. Queue only the new event at.62
instead of.52. Its reference is exactly source buffered FIR shifted earlier by.06, so it has
the same conformingV/A/J. Tail is1.42<1.70. Old history and pre-revision progress are preserved.

This.10s delay is necessary within the one-opposite-event family with separationD∈[.3,.4]:
put alpha=D/h∈[1.5,2]. The critical point has normalized old time2+alpha/2 and new time
2-alpha/2, inside the relevant spline pieces. Its acceleration is3alpha²/8-alpha. Requiring
its magnitude<=.5 forcesalpha=2. This is not an impossibility theorem for all replanners,
multi-event revisions or different allowed kernel families.

`domain_delay.lean` formalizes the polynomial identity, branch membership, necessary delay
and timing arithmetic. A physical endpoint/remain test is still required: constant disturbance
means a reference time translation alone is not enough to assert equal plant trajectories.
This candidate preserves the original task deadline and old motion; it changes only future
admission/execution timing and therefore is a new policy test.

## Decision contribution and next action

GO for an exact full-reference admission layer and a bounded physical test of the declared
.62 delayed ordinary return. A complete contract must return separate fields for reference
V/A/J, authoritative request status, causal deadline feasibility, and physical endpoint/remain.
Do not convert correct rejection into task success or compare effort on failed tasks.
HOLD on a universal competitive planner replacement: native source18/24 result is not beaten
by a gate, and neither physical deadline certification nor arbitrary replans is proved here.

Reproduce domain_fir.py with uv; it writes only domain-owned artifacts. Compile the two Lean
files with lake env lean from ctrl/lean. Scoped ruff check and format check pass. No original
research edits or integrated CLI changes. Independent critic replay requested after freezing.
Quality estimate18/20 (90%): faithful source recovery and exact reference tests; integration
and physical deadline bridge remain explicit work. Subjective confidence high for exact
reference results, undetermined for full repaired-task performance pending that test.
