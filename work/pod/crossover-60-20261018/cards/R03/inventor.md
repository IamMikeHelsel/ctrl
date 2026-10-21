# R03 inventor — a committed record is not yet faithful physical-time execution

**PAUSED checkpoint, 2026-10-19 14:04:59 UTC:** root closed the active session at the user's
request before600 substantive seconds. No PM decision exists. Recommendations and the
role grade below are provisional. No next problem or extended investigation was started.
Exact Python fixtures passed and the critic independently checked the source clock-kink
calculation/local formula. Clock-bounds four lemmas passed producer with standard axioms,
SHA2562178430283884e5a8bc28c384d8c61ea7b127884005cec48413202186528b057;
independent kernel replay remains pending. The corrected seven-lemma timewarp compile was
already running at pause; its final status must be read from the adjacent log/session.
Its failed attempts0/1 are retained and are not accepted proof evidence.

AI-written contribution; inherited root model, exact identifier unavailable.
Read the frozen stabilization addendum and actual bundle-v4 `FutureCommit.lean`,
`FutureCommitFixtures.lean`, `Kernel.lean`, and `Reference.lean`. Existing accepted scope
uses an ideal common clock and one atomic read/update. It binds exact history contents
and versions, exact task contents and versions, selected execution time, and certificate.
It preserves the actual retained reference prefix and proves reference bounds/terminal
obligations. The addendum proposes frame/calibration and uncertain-clock extensions;
these are not already fields in the original FutureCommit structures.

## Three transfers

**1. Optimistic concurrency and a transaction's linearization point.** A planning result
is a transaction against a read set: retained history, task meaning, coordinate/frame
and calibration meaning, and the clock map/validity horizon used to interpret timestamps.
The compare-and-append must be atomic against that read set, with exact candidate/event
identity retained through dispatch. This preserves the source's history equality premise;
a successful database transaction by itself does not establish that the actuator-facing
event was installed before its declared start. The domain owns state interleavings and
the root owns a concrete database test. The inventor test exposes the reference consequence
at the next boundary, without asserting an existing executor bug.

Use the source's saved moving history[(.22,.02)], width.2, and return event(.62,−.02).
Suppose the event is only installed at physical time.63, while its stored start remains.62.
The pre-install trajectory is the retained old history. Installing the already-aged event
changes the reference jet by exactly

(-1/192000000, -1/480000, -1/1600, -1/8)

in position, velocity, acceleration and jerk units. These are exact source FIR values;
the position discrepancy is tiny but nonzero. The physical robot state is not reset and
has not been simulated. Therefore the late-installed reference does not equal the actually
executed old prefix. Preserving an immutable timestamp cannot repair missed installation.

Shifting the event to.63 makes all four reference components agree at activation, but
changes the certified history and requires revalidation. This particular retimed return
still finishes at1.43, before the original deadline1.7; no deadline miss is claimed. A
library should report that change explicitly rather than silently treating the old
certificate as a certificate of the new event.

Falsifier: validate against a snapshot, then mutate its task/frame/history before a separate
append; or commit atomically but let an unbounded queue delay event installation past its
start. A single owner and a bounded, acknowledged installation protocol must cover the
actuator-facing boundary. Rejection retains the old plan; it does not prove a safe stop.

**2. Distributed-clock reasoning as a joint uncertainty problem.** Independent absolute
clock-error intervals give the sufficient inequality stated in the addendum:

estimated_commit + εc + dispatch_max ≤ estimated_execution − εe.

Exact negative: commit estimate.615 and execution estimate.625, both with error≤.005,
and dispatch.01 pass the naive estimate-only comparison. Actual commit.62, actual event
start.62, and arrival.63 obey both error bounds yet miss the start. The robust inequality
rejects because.63≤.62 is false. The test above then computes the actual reference error.

A different declared clock model can admit more: if the same affine clock C(t)=αt+β
timestamps both endpoints, with α∈[.999,1.001], the unknown common β cancels. A measured
gap.05 has physical duration at least.05/1.001=50/1001, exceeding dispatch.01 even when
an independent-error calculation with two .1 offset bounds would reject. This is an
exact improvement under extra shared-clock assumptions, not a license to cancel errors
from unrelated domains or to ignore drift. More generally the ordering check should use
the worst relative timing error over the declared joint uncertainty set. A sample-age,
drift, or validity-horizon assumption cannot be silently omitted.

For a truthful comparison, restrict β∈[−.09,.09] and physical times to[0,1]. Then each
clock error is at most.091, so the coarser independent bounds.1 are valid while still
rejecting this feasible ordering. The script checks the rational extreme parameters at
physical commit.5 and execution.5+.05/α. Shared-offset cancellation is a model refinement,
not an unexplained tightening of the same independent uncertainty box.

Falsifier: apply shared-bias cancellation to distinct clocks, or reuse a clock calibration
beyond its validity horizon. Also, changing a trajectory's time parameter has derivative
consequences, even if ordering is sound; the next transfer makes this explicit.

**3. Unexpected transfer: time reparameterization and reference regularity.** A clock is
not merely metadata if the executor evaluates the trajectory as q(C(t)). Bounded clock
offset does not bound its rate or higher derivatives. With physical time centered at
.515, define a triangular bias that is0 outside[.505,.525], rises with slope1/2 until
.515, then falls with slope−1/2. The resulting clock is continuous and strictly increasing,
with slopes1,1.5,.5,1 and uniform error≤.005. At physical.515 it reads.52.

At source phase.52 the saved moving history has reference velocity23/480. The two local
clock slopes therefore give physical-time reference velocity23/320 from the left and
23/960 from the right: a jump of−23/480. Position remains continuous. The composed reference
is not even differentiable there, despite satisfying the clock offset bound and strict
monotonicity. It cannot inherit the source's acceleration/jerk regularity contract.
This is a deliberately specified bad clock-as-phase adapter, not a theorem that all
uncertain-clock implementations fail. A clock used only to validate ordering, with
independently faithful trajectory evaluation, does not have this particular failure.

A completed exact Python variant shifts the same clock correction after the source's
saved commit.57 and timely installation.58. The correction starts.605, peaks atphysical
.615 where clock phase reaches the return event.62, and ends.625. At the peak, nominal
reference velocity1/15 becomes left1/10 and right1/30, a jump−1/15. Atphysical.614 the
clock-scaled reference jerk already exceeds the source limit7.5. This additional variant
has exact Python evidence only; it was completed before pause and is not a new formal or
physical-plant claim. It separates timely event installation from later phase-clock faults.

On the local phase interval1<z<2, the source kernel is exactly

q=(z^4−4(z−1)^4)/1200.

Relative to physical time offset s from.515, its left/right phase arguments are
z=3/2+(15/2)s and z=3/2+(5/2)s. This provides explicit polynomials and a reproducible
nondifferentiability proof, rather than a numerical finite-difference alarm.

A positive future interface follows from the chain rule. If q has bounds V,A,J and a
smooth phase θ has bounds |θ'|≤r,|θ''|≤s,|θ'''|≤k, then sufficient physical-time bounds are

|dq/dt|≤Vr,
|d²q/dt²|≤Ar²+Vs,
|d³q/dt³|≤Jr³+3Ars+Vk.

The mapping preserves the retained curve and event identity, but pays explicitly for its
time warp. It requires the stated differentiability and norm bounds; a clock-error interval
alone supplies none of them. Discontinuous clock corrections should not directly reset
trajectory phase. A disciplined monotone phase generator could be a useful next test,
with its own tracking/clock-lag budget and no reset of retained trajectory or physical state.

## Evidence and next gate

`inventor_clock.py/json` is an exact rational replay of the saved FIR formula and events.
It checks the late-install jet, retiming difference, source velocity, local time-warp jets,
clock-interval witnesses, and shared affine-clock comparison. It does not claim to invoke
the original certificate selector or validate every reference limit of a modified plan.
The kernel correspondence is a literal formula check against the inspected source.

`inventor_timewarp.lean` proves the two polynomial derivatives and nondifferentiability of
their glued local reference, plus exact clock-order arithmetic. `inventor_clock_bounds.lean`
separately checks the triangular bias bound, strict monotonicity and local affine formulas.
These isolated lemmas use ctrl's4.33 environment, not a replay of the bundle's4.35 source.
Actual producer/independent status and hashes are recorded below when complete. Failed
attempts, if any, remain saved and are not accepted evidence.

GO: compose an atomic snapshot adapter with an installation acknowledgment bound and a
specified physical-time evaluator. Mutate frame/task/history/clock calibration between
validation and install; make installation late; duplicate the queued event; and inject the
bounded triangular clock correction. Require the consumer to reject or explicitly
revalidate each changed history. Keep separate gates for state binding, ordering, reference
jet preservation, and physical tracking. HOLD on a real scheduler/actuator latency model,
clock discipline, and physical tracking premises. Quality18/20 (4,4,4,3,3); subjective
confidence98% in exact fixtures, with no hardware validation or novelty claim.


Final pause note from root: the remaining timewarp compiler was terminated at user pause; source and logs preserved. No running session remains, and seven declarations are still unaccepted. See inventor_timewarp_pause.json.
