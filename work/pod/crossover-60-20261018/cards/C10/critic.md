# C10 independent critic

## Decision and source binding

GO for finite-time enclosure plus an analytic tail as a certificate method. NO-GO for claiming a 0.2 mm tube for every admitted time-varying rate with any of the three original coefficients: explicit admitted schedules refute it. Fixed-rate positive results are useful narrower statements, not completion of the original rate-uncertain contract.

The actual short comparison uses sigma=1, jerk (+10,-10,-10,+10), four 0.02 s segments, displacement 1/6250 m, then FOUR seconds of hold (total 4.08 s). Initial physical/reference states are zero. The controller is q''-8e_x-6e_v-e_a/2+kappa*j; rate lies in [8,12]. Saved disturbance is -0.0005(1-exp(-20t)). A theorem admitting all bounded disturbances is stronger than this one saved waveform. The other cited filter-enclosure-08 report concerns a different filtered sigma10 task; its already-successful independent grader validates the arithmetic methodology, not the present task.

Source README already reported large nominal/midpoint errors for its varying-rate stress signal. Their failure is not a new discovery. The new exact switched zero-feedforward witness goes beyond the source's four tested traces, which had suggested that coefficient was favorable.

## Independent executable evidence

`critic_physical.py` imports no producer implementation. It propagates eight PHYSICAL/reference states (x,v/4,a/16,q,q'/4,q''/16,exp(-20t),1) with rational matrices, 70-digit directed integer intervals, a fixed degree-60 Taylor polynomial and a geometric infinite-tail majorant. State is retained across every reference/rate join. Whole-cell position error combines the two physical/reference coordinate series before interval summation; each theta^n ranges over [0,1], and both coordinate tail errors are included. This is ordinary exact validated computation, not a Lean proof of the algorithm or matrix-exponential/ODE correspondence.

All nine fixed-rate cases (8,10,12; kappa 0,1/10,5/48) have independently checked continuous upper bounds below 0.2 mm over the FULL 4.08 s. For kappa0 the bounds are respectively 0.119764360, 0.112905847, 0.106557550 mm. For both nonzero coefficients every bound is below 0.062545 mm. These agree with the domain's independently encoded error-coordinate calculation.

The independent physical calculation certifies:

- kappa0, rates (12,12,8,8,10) on the four jerk phases and hold: error at t=.474 is 0.3131580081582066 mm (tight outward rational endpoints in JSON), strictly above target. Full continuous upper bound is 0.313300 mm, not claimed to be the exact maximum.
- Midpoint, rates (12,8,8,12,10), SAME saved exponential disturbance: error at .474 is 2.1614617009506745 mm.
- Nominal, same second schedule and saved disturbance: error at .474 is 2.0769606418447856 mm.

These finite piecewise-constant rate schedules are admissible under the original interval bound. No controller or reference reset is required. The two switched schedules demonstrate failures for all three coefficient choices; they do not prove every possible coefficient fails.

Meaningful negative controls: the failing zeroFF run's entire motion-only bound is below 0.106264 mm and final error is only -0.062556 mm, so neither stopping at motion completion nor checking only final error establishes the required tube. Illegally resetting physical state to reference at each jerk join makes that same failing run appear to pass below 0.062520 mm. An additional 1000 exact signed interval-image checks passed, including endpoint reversal for negative multipliers.

## Positive widening, with its exact quantifier

For FIXED r=8, the error denominator is (D+4)^3. Let h(t)=t^2 exp(-4t)/2. Disturbance impulse 8h is nonnegative with integral1/8, so every measurable |w|<=1/2000 contributes at most1/16000 m from zero state. This is a hand convolution/ODE argument, not a kernel theorem.

For the source monotone reference, g=q' is nonnegative, supported on [0,.08], and integrates to D=1/6250. Matching q',q'' and zero initial values give h*j=h''*g by two integrations by parts. Since |h''|<=1, midpoint and nominal all-time bounds are respectively107/1200000 m and189/2000000 m for arbitrary bounded w, still only FIXED r=8.

The independently repeated reference-only zeroFF full-horizon bound is 0.11973778094648627 mm. For t>=4.08, every nonzero g(s) has t-s>=4; |h''(u)| <= (1+8u+8u^2)exp(-4u) <=161/65536. The majorant decreases for u>=4 and exp(16)>=2^16. Thus the later reference tail is <=161/409600000 m, smaller than the finite-time bound. Adding the arbitrary-disturbance bound gives an all-time 0.18223778094648627 mm bound for fixed r8, zeroFF and the SAME reference. This is a concrete finite-time-plus-tail improvement over the invariant cube, explicitly narrowing the rate quantifier.

## Formal audit and limits

Independently compiled all six `domain_kernel.lean` support declarations, allowed axioms only. They prove the exponential-polynomial bound, h'' bound, four source velocity positivity inequalities, polynomial total-travel arithmetic, and two numeric budgets. They do NOT formalize ODE existence, integration by parts, convolution representation, the interval program, or the final all-time trajectory statement. Final warning-only producer edit is recompiled separately and hash-recorded.

No actuator saturation, sampling, noisy state feedback, uncertain initial state, hardware or robot transfer is established. A reset or disturbance-clock restart changes the question. Finite endpoint-rate samples cannot certify arbitrary rate switching; the counterexample demonstrates that distinction directly.

Quality grade: A- for source-bound independent arithmetic and adversarial audit; B for the full positive result because its ODE/convolution and enclosure-program bridges remain hand-derived. These grades are rubric judgments, not calibrated probabilities. `critic_next_gate.json` contains 20 proposed semantic tests for a future contract adapter; it is not an executed continuation block. No original source or approved Challenge changed.
