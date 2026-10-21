# R03 root PM — atomic future publication and physical time

AI-written four-role research. Existing FutureCommit checks complete Base and Task equality, not version numbers alone. Its certificate and timing predicates are asserted at one atomic read/update in an ideal common clock. This review does not report weakened version-only or split-check counterexamples as bugs in that source. Addendum includes frame/calibration/clock identities as proposed runtime obligations.

## Three independent interfaces

1. **State publication.** The validated candidate must bind to the exact retained history, task, units, frame/calibration, clock map/epoch and owner authority. Read-set validation and append must share a linearization point. Exact structural equality is safe but can conservatively reject; version equality or hash identity needs a separate faithful binding argument.
2. **Time publication.** A clock interval must remain valid at the linearization/publication event. A read-time bound needs clock age, uncertainty growth and post-read publication tail before dispatch. Database isolation is not a bound on OS locking/fsync or delivery time. Clock-map changes are semantic state changes, not merely new timestamps.
3. **Trajectory meaning.** Ordering before an uncertain physical start does not automatically transport nominal reference bounds, exact deadlines or derivative continuity. Retimed events need a new contract. A phase clock q(C(t)) needs rate and higher derivative bounds; bounded offset alone is not enough. Frame/clock ownership must survive publication through actual actuation, including restart/replay and acknowledgement loss.

## Real local transaction experiment

pm_sqlite.py uses separate SQLite connections, BEGIN IMMEDIATE, complete canonical snapshot bytes, an append/version update and same-transaction outbox insert. Thirty-two concurrent two-writer rounds each publish exactly one update; the other and later retry reject stale state. Nine same-version history/offset/width/task/frame/calibration/clock-domain/clock-epoch/owner mutations reject. Injecting failure after history update but before outbox insert rolls both back. Independent critic replay uses a frozen byte snapshot.

This is a state-publication primitive, not a verified source certificate consumer: synthetic certificate fixture, model clock callback, and claimed10ms publication-tail allowance are explicit premises. A stale callback accepts after the modeled earliest execution time. More strongly, critic holds a real reader and measures delayed COMMIT return with a fresh callback: read-to-return exceeds the assumed tail, so post-return dispatch can already be late. This is an observed counterexample to treating10ms as established, not a theorem failure under a truthful bound. The measured endpoint is COMMIT return, not the internal durable linearization instant. No hard real-time bound is inferred from stress repetitions.

An outbox transaction cannot by itself establish exactly-once external effects: effect, lost acknowledgement, replay can duplicate an effect. The saved trace is a hand state-machine diagnostic, not a hardware experiment. Actuator-side epoch/idempotency/fencing and retained-plan semantics remain required.

## Clock as a signal, not only a label

Inventor exact source-shape example uses a continuous strictly increasing clock with≤5ms bias but a rate change1.5→.5. Evaluating retained FIR at that clock gives a velocity jump despite unchanged nominal polynomial. This is a prospective bad evaluator, not physical robot dynamics or a defect in the ideal-clock source.

Root independently adds a smooth affine negative using the actual saved moving/return event constants(.22,+.02),(.62,−.02), width.2. At phase.82 the source polynomial acceleration is−.5. C(t)=1.0001t is smooth, strictly increasing, and differs by at most.00017 over the1.7s horizon, yet physical reference acceleration becomes−.500100005. Even tiny smooth drift consumes a nonzero derivative budget. Source-polynomial/chain-rule binding is reviewed mathematics; exact Python fractions confirm values.

A useful repair is explicit chain-rule budget allocation. If the phase-reference derivatives have boundsV,A,J and clock derivatives have bounds|C′|≤s,|C″|≤r,|C‴|≤k, physical reference bounds are V*s, A*s²+V*r, J*s³+3A*s*r+V*k. pm_clock_budget.lean proves these algebraic inequalities only. Actual differentiability, chain-rule correspondence, causal monotonicity, source binding and truthful clock bounds remain premises. Even smooth monotone C with bounded offset/rate can have unbounded higher derivatives, as critic's sinusoidal construction shows.

## Sources and novelty

[SQLite isolation](https://www.sqlite.org/isolation.html) explains writer serialization and BEGIN IMMEDIATE. [SQLite atomic commit](https://www.sqlite.org/atomiccommit.html) explicitly depends on storage/locking/flush assumptions. [Herlihy–Wing1990](https://www.cs.cmu.edu/~wing/publications/HerlihyWing90.pdf) provides the linearization framework; [Spanner2012](https://www.usenix.org/system/files/conference/osdi12/osdi12-final-16.pdf) distinguishes interval time and transaction/commit-wait protocol. These are established methods, not claimed novel. The contribution is a source-specific separation and falsification of tempting implementation shortcuts.

## Direction

GO for one manifest-bound atomic publisher plus a separately declared authoritative phase-clock/dispatch contract; NO-GO for inferring robot safety from SQL atomicity or bounded timestamp offsets alone. After breadth, test payload binding, exact retained history, post-lock fresh clocks, bounded publication/delivery, frame/epoch fencing and actual start mapping. No robot, publication, billing change or public CLI integration occurred. Quality finalized in decision/card; accepted declarations only in independent ledger.
