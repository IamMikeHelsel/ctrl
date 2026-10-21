# R03 domain review — clock-aware atomic future commit

AI-written, inherited root model; exact model identifier unavailable. Domain owns only
`domain*` files. Original sources are unchanged.

## Question and strongest prior result

Can a candidate be committed only while its exact history/task/frame/timing snapshot stays
valid? The original addendum proposes this extension. The actual v4 `FutureCommit.lean`
checks complete `Base` and `Task` structural equality, a finite-candidate reference certificate,
and four timing inequalities in a common ideal clock. Its accepted transition appends the
exact event and increments history version. The resulting reference satisfies the selected
limits, retains its earlier jet, and meets its declared reference endpoint/deadline.

Its comment explicitly assumes one atomic read. Neither the offline checker nor its theorem
implements a synchronization primitive. Frames, units, calibration, clock mapping, authority
restart identity, and error-bound validity horizons are absent from the old typed structures.
The addendum proposes them; this review does not silently claim they already exist.

## Transfers and discriminating tests

1. Optimistic transaction validation: the checked object must equal the live object at the
   linearization instant, not merely at proposal or proof completion. Full equality transports
   a property; equality of a version projection alone does not. This preserves the mathematical
   object to which a certificate applies. It breaks if the actual runtime performs split reads,
   permits untracked mutations, or publishes through a separately reinterpreted queue.
2. Interval time arithmetic: latest possible commit plus publication tail and dispatch must
   precede earliest execution. If a clock read is stale, include its maximum age. A snapshot CAS
   does not detect passage of time. Offset bounds must grow with drift over their validated
   horizon. This preserves only temporal ordering, not physical interpretation of all old events.
3. Typed semantic snapshot: frame/calibration, clock-map identity, units and authority epoch
   supplement the old history/task structures. Rejecting a changed field prevents reuse under
   changed semantics, conditional on those identifiers actually binding complete meanings.

`domain_transaction.py` is an exact Fraction finite model. Source-shaped base has one event
(11/50,1/50), width1/5, return goal0, execution31/50 and delta−1/50. All nine mutations of
history, offset, width, task, frame, calibration, clock mapping, units and restart identity
retain the two old counters but are rejected by full equality. Accepted append preserves the
entire old event list; a duplicate rejects. Certificate truth is explicitly an abstract premise,
not recomputed by this model.

Timing fixture: read .57, commit/execution uncertainty .001 each, publication .003, dispatch
.01. Maximum read age is .035. At .036 the exact same snapshot must reject. Omitting any one
of uncertainty-at-commit, uncertainty-at-execution, read age, publication tail or dispatch
falsely accepts this boundary. These are exact constructed negatives, not reported runtime bugs.

## Kernel evidence and scope

`domain_clock.lean` has six producer-compiled declarations (Lean4.33.1, exit0; only standard
axioms or no axioms). They prove the interval-order implication, drift-margin monotonicity,
the exact arithmetic shape of source `timeOK`, an expired-read counterexample, property
transport through whole-snapshot equality, and a same-version/different-object counterexample.
`domain_clock_replay.log` records acceptance; the earlier log records a path setup failure.
The source `FutureCommit` dependency cache was unavailable in inspected notebook/prior-card
locations. No actual source-import bridge, fresh bundle replay, linearizability proof, or
compiled-runtime refinement is claimed. The source-interface correspondence is a hand audit.

`robust_delivery_order` places the commit linearization before the subsequent publication
and dispatch tail. Upper bounds must include pauses, queue publication and relevant scheduling;
negative allocations are disallowed by the executable model. The theorem is a conditional
arithmetic implication and intentionally does not claim these engineering bounds exist.

The old `successful_commit_contract` still requires one coordinate system for *every* event,
request, deadline and evaluation time. Plugging a physical execution interval into a nominal
pending event is not enough. A source-bound extension must validate the same actual trajectory
and its prefix/deadline under a specified mapping; it cannot backdate, move old timestamps,
reset state, or reinterpret an installed event. Equality of physical and reference progress is
not supplied here. No hardware result or general physical tracking claim follows.

## Recommendation

GO for a bounded runtime-refinement test: one actor owns the command stream; reserve an immutable
candidate token, validate complete state and a freshly bounded publication time atomically,
and publish an immutable event record carrying its clock-map identity. Independently test a
pause at every read/validate/install/publish boundary. HOLD the full physical executor theorem
until mapping, scheduler semantics, latency/drift validity and source-certificate binding exist.
Liveness additionally needs bounded candidate generation, admissible request changes and a
feasible margin; acceptance safety alone permits rejecting forever.

Domain quality: 16/20 (faithfulness4, reproducibility3, discrimination4, critique3,
actionability2). Subjective confidence: 95% in the scoped arithmetic/model findings;
not a calibrated probability of full executor correctness or novelty. These are classical
transaction and interval-order ideas, not claimed discoveries.

Sources read: paths in `domain_prep.md`; actual source `FutureCommit.lean`, fixtures and v4
README take precedence over the proposal. No primary external theorem is required for the
stated elementary arithmetic; no external novelty claim made.

## Independent critique and receipt-binding repair

The critic independently reconstructed the exact transaction cases and found an important
interface negative: modifying candidate delta to1 while retaining `checked_certificate=True`
accepts final target51/50 rather than0. This is permitted by the first model's abstract
certificate premise, but disqualifies that Boolean as a concrete acceptance interface.
The original model and negative remain preserved. `domain_certificate.py/json` adds a
trusted receipt bound to the complete snapshot/execution/delta payload; original receipt
accepts, while delta, execution and snapshot-goal mutations reject. Correct receipt issuance
and integrity remain external assumptions; the Python class is forgeable and is not an
attestation or a replacement for the source checker. Source candidate-list identity and
checker/model version would also have to accompany a real receipt where those are inputs.
The repaired finite model tests binding of the actual accepted event payload only.

## Pause and acceptance checkpoint

User requested pause before the R03 initial session reached600 substantive seconds. Root
paused its timer14:04:59UTC; no PM final decision has been made. The domain recommendation
above is advisory only. Existing critic receipt `critic_domain_clock_replay.json` independently
accepts all six domain declarations with exit0, unchanged source hash and permitted axioms.
No new research was performed after the pause; the source/executor refinement gaps remain.
