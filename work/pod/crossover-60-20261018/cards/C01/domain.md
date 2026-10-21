# C01 domain review: repairing tracking does not yet buy smoothing

AI-written domain-role analysis. Inherited root model; exact runtime identifier unavailable.
The task is a causal slow command filter meeting the fixed 0.2 mm tracking requirement while
reducing actual plant jerk or command variation relative to direct control. The experiments
below retain the frozen reference, start time, endpoint, and zero initial filter output.
They modify controller gains explicitly; none changes the task to make a pass easier.

## Recovered contract and current evidence

The frozen eight-phase rational reference is in
`/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json`.
It starts at (q,q',q'')=(0,0,0) with jerk10, receives the new goal at0.25s, retains the old
plan through0.255s, and reaches(0.6,0,0) at10491307/7508900s before holding to1.5s.
Position, velocity, acceleration and jerk are continuous at all seven joins. Snap has
one-sided phase values; using the current phase's derivative does not grant preview.

The model is x'=v, v'=a, a'=r(u+w-a). The frozen comparison uses r=80/s and w=+0.01m/s².
The separately reported direct-control theorem permits r in[80,120] and |w|<=0.01 for
supplied matched classical trajectories, but that robustness does not transfer to our new
filtered candidates. There is no actuator saturation, measurement error, sampled delay or
physical hardware acceptance in this comparison.

Put e=x-q. The original direct law is

    u=q''-800e-60e'-(1/2)e''+(1/96)j,    j=q'''.

The slow filter is u'=20(u_star-u), u(0)=0, with the same feedback and either jerk coefficient
k=1/96 or k=29/480=1/96+1/20. All plant states start at zero. Direct control is algebraic,
with u(0)=5/48; that distinction is part of the frozen comparison. We do not invent a
pre-t=0 history or reset the filtered command to its feedforward value.

The historical direct-reference package reports an all-time model bound for its direct law.
The historical filter-enclosure package gives rational Taylor enclosures proving failure
of each fixed filter at particular times, but its report labels independent review pending
and makes no Lean claim. Our numerical baseline independently reproduces the saved sampled
metrics; it does not independently certify those historical interval calculations.

## Exact augmented transfers and obstruction

Let the general filtered law use gains p,d,h, jerk coefficient k, snap coefficient l,
filter rate lambda, and z=u-q''. For a constant plant rate r,

    e''' = -r e'' + r z + r w - j,
    z' = -lambda*p*e-lambda*d*e'-lambda*h*e''-lambda*z
         +(lambda*k-1)j+lambda*l*j'.

With zero error/filter initial conditions and l=0, the exact transfer relation is

    Df(s) E(s) = r(s+lambda) W(s)
                 +(r*lambda*k-r-s-lambda) J(s),
    Df(s)=s^4+(r+lambda)s^3+r*lambda*(1+h)s^2
                 +r*lambda*d*s+r*lambda*p.

Direct control has Dd(s)=s³+r(1+h)s²+rd*s+rp and
Dd*E=rW+(r*k0-1)J. Thus adding1/lambda to the filtered jerk coefficient matches the
original direct jerk DC gain, but retains the extra -s numerator. Without compensation,
the constant-jerk equilibrium error differs by exactly -j/(lambda*p): -0.625mm for j10,
p800,lambda20. This is a sustained-input obstruction, not a theorem about every instant
of the finite frozen trajectory.

The fixed gains place the r80 direct poles at-40,-40,-40. For the augmented quartic,
its final Routh determinant is

    a3*a2*a1-a1²-a3²*a0
      =80*lambda*6400*(lambda²+25lambda-800).

All other Routh conditions are positive here when lambda>0. Stability therefore requires
lambda>(-25+5sqrt153)/2, approximately18.423/s. Lambda20 is only just above this boundary.
The filter changes feedback-loop dynamics; compensation changes reference excitation but
cannot repair those poles. The exact finite polynomial checker `domain_transfer.py` checks
characteristic coefficients and input numerators directly using determinant expansions,
including20 rational parameter cases. The general formulas above are also derived by
elimination, not inferred from those finite checks.

Adding snap feedforward changes the jerk numerator's s coefficient to r*lambda*l-1.
The choice l=1/(r*lambda) cancels that coefficient at the selected constant r. Importantly,
Laplace(j')=sJ-j(0): a nonzero initial jerk leaves the boundary forcing
-r*lambda*l*j(0). It is incorrect to claim perfect zero-error tracking by cancelling only
the J numerator while retaining the frozen u(0)=0. Our simulations integrate the actual
snap polynomial, so the initial mismatch is retained.

Every filtered candidate has e'''(0)=rw-j(0)=-46/5 at r80,w0.01, regardless of these gains,
because u(0)=a(0)=0. The direct law instead has e'''(0)=-13/15. This explains a fixed
startup cost; it does not prove that every causal smoothing controller fails the0.2mm task.

## Three predetermined feedback patterns and causal compensation

For lambda20,r80, Df's s³ coefficient is100 independently of the feedback gains. We tested
three stable real pole patterns whose sums equal100; no search continued until a lucky pass:

| Poles (negative) | p | d | h |
| --- | ---: | ---: | ---: |
| 20,20,20,40 | 200 | 35 | 5/4 |
| 25,25,25,25 | 15625/64 | 625/16 | 43/32 |
| 20,20,30,30 | 225 | 75/2 | 21/16 |

Feedback retuning alone, with k29/480 and l0, still failed tracking. The first two patterns
had sampled errors0.336539mm and0.303789mm; peak actual jerk13.5592 and13.6725; command
variation10.0807 and10.0749. Both also lost to the direct baseline on the smoothing metrics.

For joint design, the three patterns each received l1/1600 and two predetermined k values:
29/480 matches the earlier direct DC gain, while1/16 inverts the nominal r80 plant/filter
reference dynamics. These are six new controller candidates on the unchanged task.

| Design | Sampled error mm | Sampled peak actual jerk | Sampled command variation |
| --- | ---: | ---: | ---: |
| Direct baseline | 0.038465 | 10.483384 | 9.631401 |
| Original filtered baseline | 1.259612 | 30.159894 | 20.505339 |
| Compensated filtered baseline | 0.335036 | 17.511239 | 11.752551 |
| 20,20,20,40 + snap + original direct DC | 0.165958 | 12.128517 | 9.719834 |
| 20,20,20,40 + snap + nominal inverse | 0.129753 | 12.236544 | 9.674312 |
| 25,25,25,25 + snap + original direct DC | 0.148751 | 12.223039 | 9.716726 |
| 25,25,25,25 + snap + nominal inverse | 0.118380 | 12.325561 | 9.674128 |
| 20,20,30,30 + snap + original direct DC | 0.154898 | 12.187580 | 9.717926 |
| 20,20,30,30 + snap + nominal inverse | 0.122426 | 12.292413 | 9.674268 |

All six joint candidates pass the sampled tracking threshold, but none reduces either
requested smoothing metric relative to direct control. This is a useful negative gate:
meeting the tracking tolerance alone does not satisfy the user's goal. It is not a global
impossibility result for filters, other gains, or nonlinear/hybrid controllers.

## Reproduction and evidence boundary

- `domain_transfer.py`: exact Fraction polynomial determinant checks and Routh factor;
  output `domain_transfer_results.json`.
- `domain_retuned.py`: independently constructs augmented polynomial-forced systems from
  frozen reference JSON; baseline and retuned-gain results in `domain_retuned_results.json`.
- `domain_codesign.py`: six predetermined joint designs; output `domain_codesign_results.json`.
- All generated CSVs have the `domain_retuned_` prefix. Each retains the0.5ms global grid,
  exact phase boundaries and both sides of joins. Only controller state, not reference
  monomial state, is carried across phases. The reference file's hash is retained.

Numerical commands use the existing scientific Python installation through uv:

    uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/C01/domain_retuned.py
    uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/C01/domain_codesign.py

Ruff checks pass for the domain scripts. A serialization failure from a NumPy boolean in
the first run was fixed before results were saved; calculations were rerun. Sampled peaks
are not continuous-time extrema. Command variation is the sum of sampled absolute increments
on[0,1.5], with no invented pre-start command jump. These results do not certify new laws,
robustness under variable rate/disturbance, physical jerk limits, actual stopping or hardware.

## PM-relevant next direction

Reject a claim of smoothing success for these candidates. Keep the exact Routh obstruction
and the explicit startup boundary term as reusable design constraints. A useful subsequent
experiment would pose the actual jerk/command-variation objective directly, including the
fixed initial filter state, rather than optimizing tracking poles and hoping smoothing
follows. Its gains or causal correction policy must be checked on this frozen reference
and against rate uncertainty before any accepted-control claim. Domain role makes no
publication novelty claim and leaves the final GO/HOLD/NO-GO decision to the PM.

## Refined grid and analytic nominal-inverse check

The 0.25 ms refinement (`domain_gridcheck.py`, `domain_gridcheck_results.json`) reruns
only the direct baseline and the best sampled-TV candidate, four poles at -25 with
k=1/16 and l=1/1600. Direct TV is 9.63140135323107 and candidate TV is
9.674133566443487; the disadvantage survives halving the grid. Candidate peak actual
jerk is 12.32568287033146 versus direct 10.483384307099596. Candidate sampled error
is 0.1183807367884391 mm. This improves numerical resolution, not the evidence category.

The nominal inverse candidate also admits a reference-independent error formula under
its specific nominal constant-disturbance assumptions. With r=80, lambda=20, w=.01,
the chosen k and l cancel reference forcing, giving

    (D+25)^4 e = 16,
    e(0)=e'(0)=e''(0)=0, e'''(0)=-46/5.

Write c=16/390625 and S3(z)=1+z+z²/2+z³/6. Then

    e(t)=c[1-exp(-25t) S3(25t)]-(23/15)t³ exp(-25t),
    e'(t)=exp(-25t)t²(41t-23/5).

Thus e decreases until t=23/205 and increases thereafter to c=0.04096 mm. A positive
Taylor sum for exp(115/41), with a rational geometric tail bound, encloses the minimum
at -0.1183807838040449 mm and proves both extrema strictly inside ±0.2 mm in this
analytic model. `domain_nominal_formula.py` saves the rational interval and assumptions;
its formula matches the independently constructed augmented-exponential trajectory
within 8.8e-17 m on the refined grid. The critic independently derived the formula and
stationary point. This is analytic reasoning supported by exact rational arithmetic,
not a kernel-checked proof, and does not extend to uncertain rate or varying disturbance.

Tracking repair still incurs actual jerk. At t=1/20, which lies in the frozen first
constant-jerk phase, differentiating the same formula gives

    actual jerk = 10+(2157/320)exp(-5/4) > 119/10.

`domain_exact_jerk.py` encloses this quantity between 11.93122139633461 and
11.931221398109338 using only rational arithmetic and the exponential-series tail
inequality. This is a concrete non-grid overshoot witness. It alone does not certify
an upper bound for the direct baseline's continuous-time peak; that comparison remains
numerical in this domain report. Both new scripts pass scoped Ruff checks.

## Closing the continuous-time peak-jerk comparison

A subsequent analytic convolution bound closes the direct-peak limitation above,
conditional on the frozen reference's all-time |j|≤10 bound (sent to the critic for
independent reference verification). For the direct controller at nominal r=80,

    J_actual(s)=[1-s³/(6(s+40)³)]J(s)+.8 s²/(s+40)³.

The input impulse response has a delta of weight5/6 and continuous part
(40/6)exp(-x)(3-3x+x²/2), x=40t. Its negative area is

    N=[(sqrt(3)-1)exp(sqrt(3)-3)+(sqrt(3)+1)exp(-3-sqrt(3))]/6,

so its total absolute mass is 1+2N. The disturbance response is
.8 exp(-x)(1-2x+x²/2). Its extrema occur at x=0, 3±sqrt(3), or infinity;
the absolute multiplier is at most1.

Using 5/3<sqrt(3)<7/4, exp(5/4)>10/3 and exp(14/3)>64 gives
N<343/7680 and therefore

    |actual jerk_direct(t)| < 10*(4183/3840)+4/5 = 22451/1920 < 11.7.

The exponential lower bounds follow from finite positive Taylor sums and are checked
with rational arithmetic in `domain_exact_direct_bound.py`. The bound is deliberately
loose (the exact convolution estimate is about11.566901), but it separates the direct
baseline from the nominal inverse candidate's exact witness >11.9. Thus this particular
candidate has strictly worse peak actual jerk without relying on a time grid, provided
the reference jerk bound is independently validated. It still does not prove a universal
filter obstruction, and the command-TV comparison remains numerical. Scoped Ruff check
and format pass for this script. No formal-kernel acceptance is claimed.
