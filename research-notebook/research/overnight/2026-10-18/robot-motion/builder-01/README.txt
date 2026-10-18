EXACT ACCELERATION ADMISSION AND A DEADLINE-AWARE RETURN

Scope

The four-box reference uses the unchanged primitive, history, jerk checker and
real interpretation from certificate-03. This batch adds an exact rational
acceleration guard. It tests current time, future knots, and the affine-jerk
zero from each pair of future knots. Some pairs are not adjacent. Their extra
points remain in the future, so they do not affect the exact equivalence.
The implementation uses all pairs to avoid trusting an external sorter.

AccelerationGuard.lean proves checkAcceleration_real_iff. It equates a true
Boolean result with positive filter width, a nonnegative bound, and the
acceleration bound at every future real time. The proof covers constant jerk,
empty history, expired history and current time inside a knot interval.

AccelerationFixtures.lean keeps the frozen moving-goal-08 failure intact.
The immediate return passes the jerk check but reaches acceleration -21/32
m/s^2 at 0.77 s. The new acceleration guard rejects the 0.5 m/s^2 limit and
accepts the exact 21/32 m/s^2 bound. The unchanged buffered case passes exactly
at 0.5 m/s^2. Knot-only acceleration checks miss even a single event's
interior extremum. The fixtures preserve that false-acceptance witness.

ReversalProposal.lean proves a global velocity-kernel range and a velocity
bound for an equal-and-opposite two-event history. It checks a NEW delayed
return: keep the first event at 0.22 s; execute the return at 0.62 s instead
of 0.52 s. This history meets acceleration 0.5 m/s^2 and jerk 7.5 m/s^3.
Its velocity is at most 1/15 m/s. Its reference reaches exact rest at the
requested zero target at 1.42 s, before the unchanged 1.70 s deadline.
This is an explicit new proposal, not a retuned version of the old experiment.

TimedAdmission.lean defines a finite search over execution times. Each
candidate checks causality, completion of ALL retained events by the deadline,
and the all-future acceleration and jerk guards. The selected candidate has
those properties and preserves the old reference jet through its execution
time. A none result means every supplied candidate failed. It does not mean
that every possible trajectory is infeasible. No generic velocity checker is
claimed. The two-event velocity theorem covers the new return witness only.

Limits

These results concern the reference. They do not bound physical acceleration,
velocity, actuator input, torque or task settling. Existing tracking results
need explicit composition before they can support a physical position claim.
No arm, contact, inverse kinematics or Franka firmware theorem is established.
The selected time does not infer user intent. The caller supplies the current
or ready time and a correct target increment. The proof does not yet establish
that the new waiting rule improves a physical task against Ruckig.

The calculus behind polynomial extrema is established mathematics. These
proofs do not by themselves establish publication novelty.

Reproduction

Copy this directory, excluding .cache and __pycache__, to a new sibling
location before rerunning verify.py. The script refuses to overwrite its
fresh build. It copies the local source closure into an empty directory,
uses the existing Lean 4.35.0 and mathlib pin unchanged, audits every local
declaration's axioms, separately replays seven modules with leanchecker,
and requires four false statements to fail. Source hashes are checked again.
See verification.json for the actual run outcome. Compiled objects are
excluded from repository storage; their hashes are preserved.
