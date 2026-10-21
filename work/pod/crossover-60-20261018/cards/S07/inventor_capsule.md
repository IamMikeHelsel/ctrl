# Independent capsule audit

Let `E_R={z:zᵀPz≤R}` for the exact source P, `g=(1,−1,1)`, and candidate `K=E_11+[-1/8,1/8]g`. Root's `pm_quotient.lean` was read; its algebraic lemmas do not alone prove the closed-loop all-time capsule statement. The critic owns the source-bound E11 wrapper. This audit checks the lift's geometry and failure boundaries without changing those artifacts.

## The shape is genuinely different, with new active-clipping states

A simple new active state is `(59/40,−11/8,15/8)`, obtained from base `(27/20,−5/4,7/4)` by adding g/8. Base energy is43069/4000<11; lifted energy194529/16000>12. Both requests are−11/10, so the added region genuinely includes active clipping.

Conversely z=(5/4,0,0) has energy95/8<12 but lies outside K. Its best possible base energy after any allowed segment shift is35869/3200>11, attained by subtracting g/8. This follows from the quadratic `V(z−δg)=V(z)−2δ(29/10)+δ²(189/50)`: its unconstrained minimum lies at δ=145/189>1/8, so the constrained minimum is the upper endpoint. Thus K is neither a subset nor a superset of E12. Calling it an enlarged ellipsoid or a superset of the original invariant would be false.

The pure hidden point(73/40)g is another capsule point outside E12; its base(17/10)g has energy54621/5000<11 and its lifted energy1007181/80000>12. It is not the active witness above.

## Exact coupling is essential, but does not weaken arbitrary-signal coverage

The source held transition satisfies `flow(z+δg,U,t)=flow(z,U,t)+δexp(−t)g` because Ag=−g and the request functional annihilates g. Equal requests give equal clamped commands at corresponding samples. An induction can therefore propagate the identity through the same sample schedule and same disturbance sequence. At any real time, the hidden coefficient remains in[-1/8,1/8]. With a valid E11 invariant and its position bound15/8, travel is≤15/8+1/8=2.

The matching signals are a mathematical coupling: for any arbitrary admissible actual schedule and disturbance, construct the auxiliary base execution with those same signals. This does not require the real disturbance to be known or predetermined. It does not justify comparing two independently chosen schedules or disturbances.

Discriminating exact negatives:

- Changing normalized lag rate to2 makes the initial derivative residual for δ=g/8 equal(0,0,−1/8), so the exponential hidden-mode identity already fails at time0.
- Giving the paired executions different allowed disturbances0 and1/100 makes the acceleration derivative residual1/100; the request derivative gap is−1/50.
- With the earlier active center, let one execution resample at1/10 and the other hold until1/5. Both schedules are individually admitted, but the resampled command is−189/200 while the held command remains−1, giving an input gap11/200. Their common-input hidden identity cannot continue across that mismatch.

These are changed-condition negatives, not counterexamples to the proposed correctly coupled lift.

## Why the reduced base radius is needed for travel

A naive `E12+[-1/8,1/8]g` loses the source travel limit immediately. The exact base point

`(19/10,−888573/710015,622402/710015)`

has energy1004647838/88751875 between11 and12. Adding g/8 gives position81/40>2 at the initial time. The E11 choice supplies output margin; it is not dispensable bookkeeping. This also distinguishes reference/request equivalence from physical travel equivalence.

## Checks and scope

`inventor_capsule.py/json` independently solves the rational P linear system, checks both noncontainment directions, the simple active witness, the travel failure, derivative/clock negative controls, and the root's E11 disturbance/output scalar budgets. Exact arithmetic passes. The geometric constrained minimum and trajectory coupling are hand arguments; they are not claimed as a new kernel theorem. Root's11 algebraic declarations are compiled separately into `inventor_pm_quotient.log`; final status is appended once the process finishes.

GO for the fully source-bound capsule proof, conditional on the E11 wrapper, recurrence/clock assembly and explicit output reconstruction. This is an alternative shaped invariant, not a global basin, rate-uncertain certificate or hardware guarantee. Quality19/20 for the scoped independent audit.
