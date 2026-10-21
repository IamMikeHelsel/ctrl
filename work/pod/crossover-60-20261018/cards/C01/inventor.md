# C01 inventor: spend tracking margin without changing the task

AI-written, inherited root model with exact runtime identifier unavailable. Read the frozen C01 card, campaign charter, original round summary, filter-enclosure08 report and the unchanged causal-stop05 reference. No older artifact edited. Evidence here is exact rational algebra plus numerical RK4 screens, not Lean or all-time numerical certification.

The task remains the original q(t), 0.2mm tracking tube, physical state, disturbance and horizon. No preview, endpoint retargeting, early stop information or state resets are introduced. Numerical tests fix actuator rate80/s and disturbance+0.01m/s², as in the source enclosure model; they do not establish uncertain-rate/uncertain-disturbance robustness.

## Four transfers, with explicit limits

1. **Frequency-weighted model reduction / moment matching.** Treat filter memory as an actual state. Map reference jerk to position error and match low-frequency moments against the direct controller. Preserves q and causality; fails if matching a few moments is mistaken for a transient or all-frequency guarantee. Cheap falsifier: the existing compensated filter already matches the direct DC moment yet violates0.2mm. A snap-feedforward repair matches three moments; screen below shows it repairs sampled tracking while losing the jerk/variation objective.

2. **Unexpected: probability distributions of delay.** A positive causal smoothing kernel with unit integral is a delay distribution: its Laplace slope at zero is minus mean delay. Matching identity's zero mean delay with strictly positive delayed mass is impossible. Inverse derivative compensation necessarily changes that interpretation; full cancellation gives identity rather than smoothing. This is only a statement about the kernel, not the entire feedback loop. Cheap falsifier: (20/(s+20))(1+s/20)=1 exactly; calling that result improved lowpass smoothing is incorrect. The PM's derivative-bypass route is a useful related negative control.

3. **Convex certificate methods from optimization.** With fixed linear dynamics and gain k, state/error histories are affine in one snap gain l. Sampled tracking constraints intersect to an interval, jerk-squared cost is quadratic, and command variation is a weighted absolute-value sum. This permits a complete one-dimensional sampled-family comparison instead of a hopeful gain grid. Preserves task, information and initial states. Breaks at saturation, uncertain switching, or when sampled constraints are promoted to all-time bounds. Tested below: even the best sampled feasible l loses both metrics to direct control.

4. **Viability / spendable tracking-error budget.** Treat the tube as a resource, not a reason to freeze or delay the task. A governor may change actuation only while preserving the original tracking demand. The obvious robust jerk clip exposes a failure: uncertainty consumes braking authority. A gentler alternative puts a slow filter only on a feedforward correction while keeping direct stabilizing feedback. This is an explicitly changed architecture, not a rescue of the original slow output-command filter. Cheap tests: retain unknown-disturbance semantics, exact same q, and report both tracking and actual-motion metrics.

## Exact augmented transfer and startup qualification

Write e=x-q, w=u-q'', j=q'''. The fixed slow filter with an added l*q'''' term satisfies

    e''' = -80e''+80w+0.8-j
    w' = -16000e-1200e'-10e''-20w+(20k-1)j+20l*j'.

Eliminating w gives denominator

    Df(s)=s^4+100s^3+2400s²+96000s+1280000

and formal jerk-to-error numerator `(1600k-100)+(1600l-1)s`. The disturbance term is1600d in the fourth-order equation, hence16 for d=.01. Direct control with k=1/96 has E/J=−1/[6(s+40)^3].

For compensated k=29/480,l=0, DC gain agrees with direct, but the first derivative coefficient has the opposite sign. Setting l=1/1600 removes the s numerator. Since

    Df=20(s+40)^3+s³(s+80),

the snap candidate matches the direct error-series coefficients through s². `inventor_moments.py` verifies these identities exactly with Fractions and checks q,q',q'',q''' continuity at every internal frozen-reference join.

The reference starts with jerk10 while u starts0. No initial snap impulse is supplied. This startup mismatch remains in every numerical run; formal transfer-moment cancellation is not used to erase initial history. Internal snap jumps are bounded piecewise values; no smoothing of the reference is introduced.

## Numerical tests: original slow-filter family

Independent stdlib RK4 implementation uses each exact phase boundary, carries every state, and compares0.2ms and0.1ms steps. These are sensitivity checks, not rigorous enclosures. Fine-step results over the unchanged1.5s horizon:

| Law | peak absolute tracking error, mm | actual jerk² integral | command total variation | peak actual jerk |
|---|---:|---:|---:|---:|
| Direct |0.038465|83.287335|9.735572|10.483387|
| Original slow filter |1.259625|341.250058|20.505462|30.159946|
| Compensated slow filter |0.335036|121.002568|11.752594|17.511239|
| Added snap l=1/1600 |0.127315|90.751909|10.391085|12.842670|

The first two failed-filter peaks reproduce the prior enclosure locations and magnitudes numerically. The snap candidate passes sampled tracking but does not meet the full objective. Jerk² has units m²/s⁵; command variation has units m/s². The direct command's initial jump10/96 is included in its variation. There are no internal direct-command jumps because the reference jerk joins are continuous.

`inventor_affine.py` intersects every sampled tracking inequality for the entire l family. Fine-grid feasible interval is approximately[0.00035575627,0.00106286630]. Within it:

- Minimum sampled actual jerk² integral is88.936611 at l≈0.00082013621, worse than direct83.287335.
- Minimum sampled command variation is10.333829 at l≈0.00075430425, worse than direct9.735572.
- Reintegrating both optimizers matches affine predictions. The first old-plan phase has snap0, so all these l values share the same startup transient and peak-jerk obstruction.

This is a numerical NO-GO for this one-gain family, not an impossibility theorem for all filters or an exact continuous-time optimization certificate.

## Governor falsifier and relocated-filter lead

A robust instantaneous actual-jerk cap J=10.2 under unknown d∈[−.01,.01] requires

    u-a ∈ [-J/80+.01, J/80-.01]=[-.1175,.1175].

For the frozen d=+.01 realization, negative actual jerk cannot exceed magnitude8.6, while the reference requests−10 for a substantial interval. Clipping the direct command to this interval yields75.43mm peak tracking error, jerk² about121.035 and variation13.986. It respects the peak cap but plainly fails the task. This is a cheap falsifier for this governor; stronger model/state-dependent governors remain a separate question.

A more modest changed architecture keeps direct feedback and adds a causal slow feedforward state:

    z'=20(j-z), z(0)=0
    u=q''-800e-60e'-.5e''+(1/96)j+g z.

The controller receives only current reference derivatives and its existing plant error states. It does not use d. Its formal transfer is

    E/J=[-(s+20)/6+1600g]/[(s+20)(s+40)^3].

For g=1/960 this is direct E/J multiplied by(s+10)/(s+20): lower low-frequency error without changing high-frequency asymptotics. For g=1/480, DC jerk forcing cancels. Disturbance response is unchanged. This is conventional causal feedforward shaping; no novelty claimed.

Fine-step screen:

| g | peak error, mm | jerk² integral | command variation | peak actual jerk |
|---|---:|---:|---:|---:|
|0, direct baseline|0.038465|83.287335|9.735572|10.483387|
|1/960|0.029908|83.185925|9.731625|10.483153|
|1/480|0.030275|83.086243|9.729038|10.492818|
|1/320|0.036050|82.988289|9.727474|10.510781|

The g=1/960 candidate improves all displayed sampled metrics slightly; jerk² reduction≈0.122%, variation≈0.0405%, and peak-jerk change is tiny. Larger g improves integral/variation while worsening peak jerk, so “jerk improved” must specify the metric. Two grids agree on direction, but independent replay, validated bounds, coefficient uncertainty and noise sensitivity are required before claiming a useful improvement. This relocates the filter away from the feedback command; it does not demonstrate that the original slow command-filter architecture works.

## Recommendation

NO-GO for further blind tuning of the one-snap-gain original-filter family on this frozen task; its complete sampled affine-family optimum loses the requested metrics. HOLD the relocated-feedforward route for independent reproduction and exact/validated metric comparison. The modest candidate preserves task information and exposes a specific architectural next test. No general robot, hardware or robust-uncertainty claim follows.

Artifacts: `inventor_moments.py/.json`, `inventor_screen.py/.json`, `inventor_affine.py/.json`, `inventor_relocated.py/.json`. All Python runs through uv. Parent PM owns final grading and decision.

## Fixed-gain robustness screen and admissible-family boundary

At the PM's request, `inventor_robustness.py` predeclares g=1/960 without retuning, rates80,100,120 and disturbances−.01,0,+.01, comparing matched direct control for every case. Every case runs at0.1ms and0.05ms. Controller coefficients, beta20, initial z0, causal q, event times, horizon and error target stay fixed. Plant rate/disturbance affect only the simulated plant; neither is supplied to the policy.

All nine candidates pass the sampled tracking test; maximum observed candidate error is0.0510713mm. Across the nine refined runs, paired differences(candidate−direct) are:

- Jerk² integral: −0.102178 to−0.098884; improves in all nine.
- Command variation: −0.003948 to−0.001379; improves in all nine.
- Peak jerk worsens by0.0227174 at(80,−.01) and0.0429785 at(100,−.01), is essentially unchanged in several cases, and slightly improves in two.
- Peak tracking error increases at rates100/120, though remains within the fixed tube.

Halving the grid changes paired integral differences by at most3.50e−7 and variation differences by6.50e−7. This supports numerical reproducibility, not a rigorous error estimate or universal robustness between the nine sampled parameter cases. The favorable integral/variation directions do not justify saying peak jerk improves robustly.

A filter's nominal rate20 does not by itself constrain its output derivative: arbitrarily large or derivative-compensated input can defeat a smoothing interpretation. The admitted relocated family here is explicitly

    direct command + g z, z'=20(j-z), z0=0,

with fixed g=1/960. It is not an arbitrary input into the original command lowpass and does not bound all actuator-command derivatives. The original command-filter family and this architecture must remain separate in the decision board.

## An all-time model tracking bound at rate80

A stronger tracking argument is available for this relocated candidate, independent of the favorable sample grid. With zero e,e',e'',z initially,

    (D+40)^3 e = -j/6+z/12+80d,
    z'=20(j-z).

For any measurable bounded jerk |j|<=10 and disturbance |d|<=1/100, the causal positive filter gives |z|<=10. Hence forcing magnitude is at most

    10/6+10/12+80/100 = 33/10.

The impulse response of1/(s+40)^3 is t² exp(-40t)/2 for t>=0; it is nonnegative and its integral is1/64000. The convolution estimate therefore gives

    |e(t)| <= 33/640000 m = 0.0515625mm < 0.2mm.

`inventor_tracking_bound.py` exactly checks the frozen reference's jerk bound by converting its actual rational polynomials to Bernstein form on64 rational subintervals; every coefficient lies in[−10,10]. It records the coefficients and the rational final budget. Internal reference jerk continuity was checked separately, and the initial jerk step is permitted by this bounded-input argument without a snap impulse.

This is an ordinary mathematical derivation under the specified linear ODE/convolution and initial-state assumptions. The coefficient arithmetic is exact; the ODE/convolution proof and program are not Lean-checked. It covers rate80 and bounded time-varying disturbance, but does not establish jerk/variation improvement, uncertain rates or hardware tracking. Independent review is still needed before formal promotion.
