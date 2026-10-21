# C02 domain: optimize the actual error response, not its forcing surrogate

AI-written domain research; inherited root model, exact identifier unavailable. Original
sources and approved challenges preserved. No architecture change or hardware work.

## Exact source binding

Read `source_snapshot.txt`, the original `TrackingReplan.lean` and `comparison.py` under
`/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/tracking-replans/`.
Plant: x'=v, v'=a, a'=r(t)(u+w-a). Controller:

    u=q''-8σ²e-6σe'-e''/2+κj,    e=x-q,    j=q'''.

Consequently

    e'''+(3r/2)e''+6rσe'+8rσ²e=(rκ-1)j+rw.

There is no slow command filter here. This is the original acceleration-feedforward and
jerk-feedforward controller. The source comparison uses a four-piece constant-jerk
reference (+J,-J,-J,+J), equal segment length h, followed by a 4 s hold. It reports sampled
peak position error over that full interval for fixed rates 8σ,10σ,12σ and one declared
varying-rate stress signal; initial error is zero, disturbances are either zero or a fixed
bounded rising signal. These are not all possible adversarial rates/disturbances.

The source already proves reciprocal-midpoint optimality for the invariant-cube residual
and nominal-reciprocal optimality for the initial-jerk minimax. Neither establishes a
universal position-error optimum. Those prior statements remain intact.

## Affine-response bridge

For any prescribed rate function, disturbance and initial state independent of κ, the
state matrix is independent of κ and the forcing is affine in κ. Thus eκ(t)=a(t)+κb(t),
where a is the κ=0 trajectory and b is the zero-initial-state sensitivity driven by r(t)j(t).
This is valid for a fixed varying-rate scenario as well as a constant rate, with the usual
linear ODE solution assumptions. The coefficient does not alter the actual rate signal.

Finite-horizon squared position error is Aκ²+2Bκ+C, where A=integral b²,
B=integral ab, C=integral a²; if A>0 its minimizer is -B/A. If A=0, κ has no effect in
that metric. A restricted coefficient range requires projection onto that range. Peak
position error is the convex scalar problem minκ sup_t |a(t)+κb(t)|. Two certified basis
responses can therefore replace an unrestricted integration sweep over κ. A finite set
of scenarios gives the maximum of their convex objectives; it is not the robust optimum
over every allowed rate signal.

For constant r, zero initial error and w=0, this simplifies much further:

    eκ=(rκ-1)f_r,    L_r f_r=j,    zero initial state.

Hence κ=1/r gives zero error for every reference and horizon in this ideal model. For
any homogeneous norm, the ranking of other coefficients is determined solely by
|rκ-1|. There is no fixed-r, zero-disturbance ranking reversal caused by changing the
horizon or reference. In particular, at r=12σ the midpoint has 1.25 times the nominal
error. Over r in [8σ,12σ], both nonzero competitors have forcing magnitude at most1/4,
whereas κ=0 has magnitude1. A claimed fixed-r, zero-disturbance win for κ=0 would contradict
this model. The source's zero-feedforward win includes varying rate and/or disturbance.

## Declared polynomial probe and low-order series

To expose finite-horizon weighting analytically, use a **new declared reference**
q=D(10s³-15s⁴+6s⁵), s=t/T, over0<=t<=T. It has zero initial/final velocity and acceleration.
It is not the source's four-piece jerk reference. With zero initial error and disturbance,

    eκ=(rκ-1)D[10t³/T³
      -(15/T⁴+15r/(4T³))t⁴
      +(6/T⁵+9r/(2T⁴)+(9r²/8-3rσ)/T³)t⁵+O(t⁶)].

For the source's first constant-jerk segment instead,

    eκ=(rκ-1)J[t³/6-r*t⁴/16+(3r²/160-rσ/20)t⁵+O(t⁶)].

The series do not by themselves control the whole motion. The following test does:
`domain_response.py` integrates a degree60 Taylor expansion of the matrix exponential
kernel against the exact quadratic jerk polynomial using Fraction arithmetic. In normalized
s coordinates, the companion matrix has row norm
K=max(1,3rT/2+6rσT²+8rσ²T³), and |Q'''|<=60. An explicit uniform remainder is

    epsilon = 60*3^ceil(K)*K^61/(61!*62),

using exp(K)<=3^ceil(K). The squared-L2 integral of the polynomial is exact and differs
from the true integral by at most epsilon*(2 sum|polynomial coefficients|+epsilon).
Square roots are enclosed by rational floor-root inequalities. For the peak metric, the
polynomial is converted to Bernstein form and subdivided into64 dyadic intervals exactly;
control coefficients give the upper bound and endpoint values the lower bound, adjusted
by epsilon. These are independently reproducible analytic enclosures, not Lean-checked
ODE/integration certificates.

## Exact discriminating result

Fix σ=1, r in the **two-point set {8,12}**, zero disturbance and initial error. Optimize
worst error over those two fixed-rate plants. For either norm, if Ar and Br are the two
positive unit-forcing response norms, the minimizer is

    κ*=(A8+A12)/(8A8+12A12).

This balances the weighted endpoint errors. It does not assume the continuum's worst
rate lies at an endpoint.

| Motion T | Two-rate squared-L2 optimum κ interval | Motion-peak optimum κ interval |
|---|---|---|
|0.08 s|[0.10137586527800278,0.10137586527805034]|[0.10144751769904367,0.10145018941696471]|
|0.25 s|[0.10318124119038215,0.1031812411904814]|[0.1028716770413352,0.10287917846909586]|

The displayed decimal endpoints are rounded representations; exact rational intervals
are authoritative in `domain_response_results.json`.

At T=.08, nominal beats midpoint in both metrics. Exact normalized motion-peak bounds:
nominal [0.13730314,0.13733595], midpoint [0.14876733,0.14877061]. At T=.25, midpoint
beats nominal: [0.07155520,0.07158486] versus [0.07584757,0.07587098]. Zero jerk FF is
worse in both. Full exact bounds and all three L2 values are in JSON.

This is a **two-rate robust ranking reversal across two reference durations**, not a
fixed-rate ranking reversal. It decisively shows that finite-horizon response weighting
can move the optimum away from both preselected surrogate coefficients. The initial
blanket prediction that nominal would beat midpoint at both durations failed; the draft
with that false assertion is preserved in `domain_response_failed_prediction.py`.

## Original peak objective remains a separate obligation

The certified peak above ends at motion completion T. The original comparison includes
a4s hold and a different reference. `domain_hold_probe.py`, run with the already installed
`/usr/local/bin/python3` through uv, numerically samples the new quintic's extra hold and
finds no larger peak. This is only a supplementary probe, saved in its own JSON. The
source's invariant-cube radius initialized at T is too loose to certify that fact. Neither
the new reference nor a motion-only enclosure is silently substituted for the frozen
benchmark. A certified hold propagation is required to close even this quintic full-horizon
claim; the original benchmark then needs its own paired basis computation.

## Formal pieces, crossovers and scope

`domain_affine.lean` compiles three scalar algebra lemmas: quadratic completion, its lower
bound at the minimizing value, and reciprocal-rate residual cancellation. Only standard
axioms occur. These do not prove the ODE affine bridge, kernel remainder, or Bernstein
implementation. The failed first compile is retained; final log records successful audit.

Transfers: (1) linear-system superposition turns coefficient search into basis identification;
(2) Chebyshev approximation turns peak tuning into scalar convex minimax; (3) verified
numerics/Bezier control polygons turn finite-horizon peak comparisons into interval evidence.
Each preserves the actual trajectory objective only when its reference, horizon and scenario
set remain explicit. A missing rate scenario or omitted hold can invalidate a robust claim.
The linear systems mechanism is standard background; see the primary
[Boyd and Lall linear dynamical systems lecture](https://ee263.stanford.edu/lectures/linsys.pdf).
No novelty claim or measured robot conclusion is made.

## Domain recommendation

GO for an objective-specific two-basis certificate on the unchanged source benchmark,
including the4s hold, then additional fixed/varying-rate scenarios. HOLD on a universal
robust-optimal coefficient: arbitrary varying-rate and disturbance optimization is not
resolved. A precise next falsifier is a certified third rate or hold extremum that changes
the proposed coefficient's ranking. Keep the existing invariant certificate as a separate
safety bound while testing actual finite-horizon error.

Quality estimate: faithfulness4, reproducibility4, discrimination4, critique4, actionability3
=19/20 (95%). Subjective confidence high in the conditional algebra and exact two-rate
probe, moderate in usefulness for the unchanged benchmark, low in any universal optimizer.
PM owns the final decision and timing.
