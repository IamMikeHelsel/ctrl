# C10 — Finite tracking tubes and the actuator-rate quantifier

**PM decision: GO for a source-bound finite-tube certificate and the fixed-rate all-time result. NO-GO for a0.2mm guarantee over the full varying-rate family with any of the three tested original coefficients.** This does not rule out every controller. AI-written initial pod review; substantive timing is in state.json.

## Frozen question and provenance

Can a finite-horizon tube certify the short-move task that a global invariant cube makes excessively conservative?

Sources: `research/adjacent-controls/tracking-replans/README.txt` and `research/pods/2026-10-17/controls/filter-enclosure-08/builder/report.txt` under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes`. Frozen/current hashes are recorded in source_binding.json. The tracking comparison supplies the actual task; filter-enclosure supplies a validated Taylor methodology for a different filtered model, not a substitute task. Its builder pending-review wording is historical; the critic inspected the existing grader's acceptance.

Original short move: scalar x'=v,v'=a,a'=r(u+w−a), sigma1, r in[8,12]/s; four constant jerk phases(+10,−10,−10,+10)m/s³, each1/50s, then4s hold. Displacement1/6250m=0.16mm, total horizon102/25s=4.08s. Initial physical/reference errors are zero and state is retained at every join. The three existing coefficients are κ=0,1/10,5/48 in `u=q''−8ex−6ev−ea/2+κj`. The saved comparison disturbance is `w=−(1/2000)(1−exp(−20t))`; the theorem's broader uncertainty permits arbitrary |w|≤1/2000.

Prior global tilted-cube bounds are valid conditional results but large: midpoint R1253/12000m≈104.417mm, κ0 R0.62525m. Prior sampled varying-rate runs already showed midpoint/nominal failure; they did not show the new κ0 counterexample below. No changed gains, actuator-speed assumption, shortened hold or physical reset is used in accepted original-task comparisons.

## Three transfers

1. **Validated reachability and translation validation:** propagate exact outward Taylor intervals and a uniform remainder on every cell, with a separate physical-coordinate implementation. Preserve phase state, exponential disturbance state and complete horizon. This certifies named trajectories continuously, unlike dense samples.
2. **Signal geometry rather than peak jerk alone:** at fixed r8, the error denominator is(s+4)^3. Integrating the jerk convolution twice transfers the forcing budget to reference velocity and its total variation. The original move is monotone, so total variation equals its0.16mm displacement. This yields an all-time bound with arbitrary bounded disturbance; the ODE/convolution bridge remains a hand derivation.
3. **Unexpected adversarial scheduling:** actuator-rate variation can correlate with reference phases and turn signed forcing cancellation into accumulation. Constant-rate endpoint tests therefore do not bound time-varying rates. A reversing-reference negative also shows that total variation cannot generally be replaced by net endpoint displacement.

## Continuous enclosures and independent checks

Domain uses a five-state error/exponential system,100-digit integer intervals, exact rational matrices and adaptive Taylor degree with a proven geometric bound on the infinite tail. A cell tube encloses every local time, not just the endpoint. The critic independently uses eight scaled PHYSICAL/reference states,70-digit intervals and fixed degree60 with its own tail calculation; no producer matrices or interval routines are imported. Both retain all states across the four joins and the4-second hold.

All nine combinations of fixed r8,10,12 and the three existing coefficients pass the0.2mm position tube over the full4.08s, for the saved exponential disturbance. Worst per coefficient: κ0≤0.119764360mm, nominal≤0.062544009mm, midpoint≤0.062542290mm. These are nine specified fixed-rate cases, not a proof for every constant r in[8,12], arbitrary time-varying r, arbitrary w, or physical hardware.

An admitted piecewise-rate counterexample defeats each controller. At t237/500s=0.474s, retaining the SAME original exponential disturbance:

| Original coefficient | Rates on four motion phases, then hold | Exact independently enclosed error, approximately |
| --- | --- | ---: |
|0|12,12,8,8; then10|+0.3131580081582066mm|
|1/10|12,8,8,12; then10|+2.0769606418447856mm|
|5/48|12,8,8,12; then10|+2.1614617009506745mm|

For κ0, the inventor's outward interval in meters is[0.000313158008158206,0.000313158008158207]; the critic's physical-coordinate enclosure agrees. Each exceeds0.0002m. All rate changes lie at original reference phase boundaries, states remain continuous, and rates remain inside[8,12]. No new global-maximum claim follows from these witnesses. Root's separate768-schedule floating-point screen only selected candidates; it is not the acceptance evidence.

Useful failures: the κ0 counterexample's motion-only bound is0.106264mm, and its final error is about−0.062556mm. Both an80ms-only check and an endpoint-only check miss the later violation. Illegally resetting the physical state to the reference at joins falsely gives a full-horizon bound below0.062520mm. Signed interval rounding and finite-tail omission are independently challenged.

## Stronger fixed-r8 result with arbitrary bounded disturbance

Let h(t)=t²exp(−4t)/2. For the unchanged reference, g=q' is nonnegative, supported on[0,0.08], and ∫g=D=1/6250. With zero initial errors, the hand-derived convolution identity is

`e=(8κ−1)(h'' * g)+8(h * w)`.

Here |h''|≤1, h≥0 and ∫h=1/64, yielding `|e|≤|8κ−1|D+W/8` for all time. It gives midpoint107/1200000m=0.0891667mm and nominal189/2000000m=0.0945mm. The simple κ0 bound0.2225mm fails the target; this is conservatism, not a counterexample at fixed r8.

For κ0, root separately encloses the disturbance-free reference response over4.08s by0.119737781mm, independently reproduced in physical coordinates. After4.08s, all kernel ages are at least4s; `|h''(s)|≤(1+8s+8s²)exp(−4s)≤161/65536`, so reference error≤161/409600000m. Adding the arbitrary-disturbance budgetW/8 gives the all-time bound **0.182237781mm**. This is fixed r8 only and assumes trajectories satisfying the original continuous-feedback model. It establishes no sampled implementation, saturation, contact or robot result.

The monotonicity premise matters: a changed-task diagnostic concatenates the original forward short move and its reverse. Net displacement at0.16s is zero, total variation0.32mm, but exact error is about0.013266840323065mm for fixed r8, midpoint and w0. This refutes a zero-net-displacement bound; it is not an original-task failure.

## Formal boundary, grade and next step

Six supporting Lean declarations in domain_kernel.lean were independently compiled/audited: the exponential-polynomial envelope, the h'' expression bound, nonnegative reference-velocity pieces, polynomial total-travel arithmetic and two exact controller budgets. Only propext, Classical.choice and Quot.sound occur. The complete source-function integral, Duhamel/integration-by-parts identity, existence/refinement, Taylor-series program and physical model are not all assembled as a kernel theorem. Exact arithmetic and independent continuous enclosures are a different evidence tier from the six kernel helpers.

Quality rubric: faithfulness4, reproducibility4, discriminatory value4, independent critique4, actionability3 = **19/20,95%**. Subjective confidence is high in the independently reproduced bounds and counterexamples. The critic grades the complete positive proof chain B because bridges remain hand-derived; no calibrated probability or novelty claim is made.

After all60 initial reviews, use one30-minute block to bind the full original reference/ODE to a serialized continuous-tube consumer and the fixed-r8 convolution bridge, with20 semantic mutations. Preserve arbitrary-rate counterexamples as mandatory rejection controls. A full-band controller redesign or new rate-variation assumption is a separate contract change, not a relabeling of these successful fixed-rate cases. Keep original files, approved challenges and controller alternatives unchanged; no hardware or external action.

Detailed evidence: domain.md, inventor.md, critic.md; domain_enclose.json, critic_physical.json, critic_supplement.json, inventor_zero_ff.json, pm_reference_only.json, inventor_variation.json and Lean logs. Root's numerical schedule search is explicitly labeled a screen.
