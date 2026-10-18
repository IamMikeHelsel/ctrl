What changed when the sources became distinguishable
===================================================
This is a synthetic, signed, single-phase amplitude example. It is not a vehicle
model, a complete wheel-balance calculation, or a safe spin-up/down controller.
All model constants, readings, action choices and acceptance limits were saved
in model.json BEFORE the first result was computed. Its SHA-256 is
9f2ff239496551e75477405e91048a69d91eb3759d949a94501e3ebc13d9b867.

Result
------
                       Possible wheel contribution w       Correction -1/2
Baseline               [-11/10, 2]                         Not certified
Duplicate reading      [-11/10, 2]                         Not certified
Known trial +1/2       [-11/10, 2]                         Not certified
Separating reading     [27/70, 47/80]                      Accepted

After separation, correction c=-1/2 has worst wheel-component residual 4/35
(about 0.11429), below the predeclared 1/8 limit. For every retained source tuple
and every mixing coefficient rho in [0,1], |w+c+rho*d| is at most 3/5, below the
predeclared 3/4 limit. Both conditions are required for acceptance.

The other predeclared action, c=-1 (cancel the nominal baseline reading), fails
the wheel-component requirement even after separation. Its worst residual is
43/70. A concrete retained witness is w=d=1/2, lambda=1/4: c=-1 leaves a wheel
component of -1/2. This shows why cancellation of the total observed signal is
not a certificate of correct source attribution.

Model and intervention
----------------------
Unknown signed wheel and drivetrain components w,d lie in [-2,2]. Baseline
response is w+d, observed as 1 with error at most 1/10. The phase convention and
wheel gain 1 are FIXED AND KNOWN. Thus the trial is a consistency/redundancy
demonstration here, not estimation of an unknown gain. Adding wheel component
1/2 gives reading 3/2 with the same error bound. Subtracting the known addition
leaves exactly the same strip in this chosen data set. Other trial noise values
could tighten the sum strip, but the common row (1,1) still cannot distinguish
the two sources. The duplicate is literally the same observation and its error.

In the separating condition, the readout is w+lambda*d. A calibrated real
cross-leakage coefficient lambda lies in [1/5,3/10]. Its observed value is 5/8
with error at most 1/40. One possible interpretation is an order-tracked readout
after changing relative rotating frequencies. The leakage interval is an
ASSUMPTION; no window/filter implementation or vehicle is claimed to produce it.
In particular, an ordinary common speed sweep need not separate equal orders.

The same lambda persists across readings, including the held-out readout
w+(lambda/2)*d. That exact factor-of-two relation is also an explicit calibration
assumption, not a general law of demodulation. Source amplitudes and support
transfer paths are assumed unchanged across conditions and trial/correction.
If changing the operating condition changes them, this model must be revised.

How the bounds are obtained
---------------------------
Lift q=lambda*d, and split the feasible set into d>=0 and d<=0. In each branch,
the product constraint is exactly linear:
  d>=0: d/5 <= q <= 3d/10;
  d<=0: 3d/10 <= q <= d/5.
For d nonzero, lambda=q/d recovers a valid common coefficient. For d=0 the
constraints force q=0 and any allowed lambda suffices. Therefore the lifted
union represents the sources and their shared leakage exactly for these rows.
This is not an independent box relaxation of q, lambda and d.

experiment.py enumerates intersections of triples of rational constraint planes.
Every reported endpoint has a feasible witness and a nonnegative dual linear
combination proving the corresponding bound for ALL feasible points. The empty
negative-d branch after separation has a Farkas combination proving 0<=-1.
check.py independently verifies these saved combinations with Fraction arithmetic;
it does not repeat the vertex search. Tightness follows from the witnesses, so
acceptance does not rely on a grid or on having sampled enough source states.
The complete model set must be nonempty before any action is accepted.

The mixed-response maximum uses the endpoints rho=0,1, since absolute value of
an affine function is convex. This gives a uniform static bound, not a dynamic
bound during test excitation or correction installation.

Held-out checks
---------------
The held-out condition is NOT used in identification. Its exact predicted range
is [69/140,99/160], about [0.492857,0.61875]. The prescribed good reading 9/16
with error 1/40 gives interval [43/80,47/80]. These intervals overlap. This is
EXISTENTIAL consistency: some retained tuple fits. It does not mean that every
retained tuple fits, that the whole prediction interval lies in the observation
interval, or that physical conformance has been validated. The illustrative
truth w=d=1/2,lambda=1/4 produces all nominal readings exactly and was not given
to the estimator.

A second, deliberately inconsistent held-out reading 4/5 +/- 1/40 gives
[31/40,33/40], disjoint from the prediction. The declared model/data contract is
rejected for that case; it is not repaired by silently enlarging the bounds.
Both held-out cases and both correction outcomes are retained in results.json.

Reproduction and evidence
-------------------------
From the workspace root:
  python3 research/adjacent-controls/source-attribution/experiment.py
  python3 research/adjacent-controls/source-attribution/check.py
  python3 research/adjacent-controls/source-attribution/negative_checks.py
  python3 research/adjacent-controls/source-attribution/figure.py

The run uses Python's standard library only. results.json includes model/script
hashes, all constraint rows, vertices, 56 bound certificates, one infeasibility
certificate, eight action evaluations and timing. The checker passes. These are
exact mathematical computations checked by Python, NOT Lean kernel proofs.

The hardened checker requires all four stages, both sign branches, all four
objectives/ranges and both actions. It pins the original model hash, reconstructs
prior bounds from that model, checks actual certificate counts, and verifies the
held-out and duplicate/trial summaries. It refuses Python -O because that option
disables its assertions. It can check a disposable result via --input PATH.
negative_checks.py confirms rejection of missing coverage, changed endpoints or
dual weights, forged empty-set acceptance, false action/held-out decisions and
other binding errors. Fourteen negative cases pass; negative-checks.json records
the exact errors and source hashes. The original result and model stay unchanged.
The empty-set corruption is rejected by invalid Farkas evidence before an action
is considered; the checker also explicitly requires a surviving feasible branch.

Limits and value
----------------
There is no full complex/quadrature component, full imbalance magnitude, actuator
lag, transient safety, sensor hardware, fitted transfer function, or vehicle
validation here. Error bounds, transfer calibration and source stationarity must
come from outside this demonstration. Accepted means the two declared scalar
conditions hold for the nonempty retained set under this model.

Useful result: joint uncertainty and a separating intervention can change a
concrete correction decision while repeated evidence and trial subtraction
cannot invent source information. This is a small reproducible example of a
known identification principle, not a novelty claim. Extending it to a useful
controls theorem needs a sound dynamic model for the intervention and its safe
termination, not just the static source estimates.
