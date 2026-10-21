# C01 independent critique

Role: independent critic/checker. Inherited root model; exact runtime model identity unavailable. AI-written research notes. Numerical results below are separate from exact rational enclosures, Lean proofs, novelty assessment, and hardware validation.

## Binding and fairness

The source task fixes the causal reference, goal arrival at 0.25 s, old-plan hold to 0.255 s, 0.6 m goal, deadline 10491307/7508900 s, and hold to 1.5 s. Position tolerance is 0.0002 m throughout and at the deadline. Reference q/v/a/j joins are continuous; snap can jump. Plant is x'=v, v'=a, a'=80(u+0.01-a), all physical states initially zero. Direct feedback initially commands 5/48; both original full-command filters initially command zero. Equal physical initial states is the appropriate comparison; forcing algebraic direct control to start at zero changes its law. No pre-time-zero command history was specified. Do not invent a startup jump in one total-variation metric and omit it in another. Physical stopping velocity/acceleration tolerance was not supplied, and no hardware test is present.

Reference SHA256: `0afc2c547033e22570711ea63a4d62c8a4380499c62a5da3f644de04fce5ad02`.

Original sources read: admission-04/grader-preflight/preflight.txt; causal-stop-05/builder/{report.txt,reference.json}; filter-enclosure-08/{builder/report.txt,builder/enclose.py,grader/report.txt,grader/mathematical-audit.txt,grader/independent_enclosure.py}, all below `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/`.

## Exact old failures reproduced

The builder's pending-review note is stale: the original independent grader accepted the enclosure as grade A. `critic_replay_old.py` re-executed that independent implementation without writing original files. It recovered:

- Old filter, t=171/400: error in [0.001259612313705,0.001259612313706] m.
- Compensated filter, t=1581/2000: error in [0.000335036376680,0.000335036376681] m.

Both strictly violate 0.0002 m. These are exact rational interval/Taylor computations independently replayed in Python, not Lean kernel proofs. Corrupted dynamics, filter initial condition, and timestamp certificates were rejected. Saved result: critic_old_enclosure_replay.json.

## Independent algebra

For U_k=q''-800e-60e'+0.5(q''-a)+k j, filtered u'=20(U_k-u), the general scalar error equation is

`e''''+(r+lambda)e'''+r lambda(1+ka)e''+r lambda kd e'+r lambda kp e = (r lambda k-lambda-r)j-j'+r lambda w+r w'`.

Its transfer denominator at the frozen gains is `s^4+100s^3+2400s^2+96000s+1280000`. Reference-jerk numerator is `-s+1600k-100`. Old k=1/96 gives `-s-250/3`; compensated k=29/480 gives `-s-10/3`. Direct error transfer is `(-1/6)/(s^3+120s^2+4800s+64000)`. Compensation matches direct DC jerk gain -1/384000, but neither the snap coefficient nor the poles. Zero physical initial states do not mean all scalar error derivatives vanish. Initial error third derivatives are -13/15 direct and -46/5 filtered.

`critic_transfer.py` checked 15 rational state-resolvent identities without producer functions. The final Routh determinant is `(80 lambda)*6400*(lambda^2+25lambda-800)`, with the other Hurwitz conditions automatic for positive lambda. Thus lambda must exceed (-25+5 sqrt153)/2, approximately 18.423. The frozen lambda20 is close to this boundary. The feedforward jerk coefficient changes numerator, not poles. This is an exact algebraic diagnosis, not a robust nonlinear guarantee.

## Independent new experiment checks

`critic_reintegrate.py` used physical coordinates and DOP853, without producer functions, to compare all 15,050 saved rows for direct, old, compensated, and two pole-retuned laws. Maximum discrepancy across x/e/e'/e''/u/actual jerk was below 3.95e-11. Pole-retuned maximum errors 0.33654 and 0.30379 mm still fail. Filter memory was retained across reference joins.

`critic_bypass.py` independently reproduced all six root derivative-blend laws, maxima and command variation within 4.8e-11. The expanded coefficients in pm_bypass.py are correct. The direct derivative includes the actual plant correction; filtered laws use nominal 80(u-a), without an oracle for unknown disturbance. Alpha0 is the old compensated filter; alpha1 is an estimated derivative bypass. Intermediate alpha can meet sampled tracking, but none of the tested values beats direct peak actual jerk or TV. A deliberate filter-state reset at joins produced 3.3865 mm error and jerk256; deleting the derivative's -800e' term also failed reproduction. Saved negative controls demonstrate that retained memory and coefficient mapping are consequential.

The snap-family inventor uses an initial direct-command jump of 10/96 in TV. Subtracting this restores the historical direct baseline near9.6314056; its sampled best TV remains10.333829 and jerk-squared integral88.936611 versus direct83.287335. The convention therefore strengthens the negative result but must be harmonized. The family optimum is for one sampled one-parameter family, not a universal impossibility certificate. Snap compensation changes the controller architecture and requires current reference snap, which is available; it does not grant future preview.

## Interpretation and proposed gate

NO-GO for the original two frozen forced filters: exact failure is established. NO-GO for promoting the tested simple pole-retunes or derivative blends as improvements: either tracking fails or the smoothness objective worsens. Do not infer impossibility for all causal slow-filter architectures.

A relocated filter acting on reference jerk while retaining direct feedback is a distinct two-degree-of-freedom architecture, not a repair proof for the original full-command filter. It preserves reference/task/physical initial state and causality, but retains fast direct feedback and therefore does not establish that the entire command channel has slow bandwidth. Tiny numerical benefits merit a bounded GO only with explicit architecture labeling, independently reproduced metrics, all-time bounds, and perturbation tests. Sensor noise, saturation, derivative measurement, rate uncertainty, timing, and physical robot validation remain untested.

Rubric for this critic artifact: source binding4/4, independent algebra4/4, reproduction4/4, failure controls4/4, acceptance limits4/4 =20/20. Subjective confidence: high in the exact reproduced historical failure; low in practical new-controller benefit pending exact bounds and robustness. No calibrated success probability is asserted. This is a grading of evidence handling, not probability of solving C01.

### Relocated-filter independent reproduction

`critic_relocated.py` independently integrated physical x/v/a and the reference filter state using DOP853, with no producer imports, matching all four gains within2.85e-11 on the inventor's 0.1 ms grid. For gain1/960: maximum error0.0299084 mm; peak actual jerk10.4831526 versus direct10.4833867; command TV excluding the common startup jump9.6274584 versus9.6314056; jerk-squared integral83.1859253 versus83.2873353. Relative improvements are approximately0.00223%,0.0410%,0.122%, respectively. Gains1/480 and1/320 improve TV and integrated jerk further but increase peak jerk; objectives must not be conflated. These are numerical finite-grid results. The very small peak-jerk benefit particularly needs verified extrema and perturbation margins before promotion. No claim of novelty or physical benefit follows from this replay.

All five critic Python scripts pass scoped Ruff lint and formatting checks. Full repository checks are parent-owned; no public CLI, approved challenge, or original research source was edited.

### Continued initial-session bounds and gate correction

The original C01 question remains OPEN. The old two full-command filters are rejected, as are the tested routes advertised as improvements; neither the architecture class nor the original problem is closed. Under the user's rule against changing the question, the relocated reference filter should be labeled an ALTERNATIVE research lead. It must not be counted as a successful slow full-command filter. A PM can retain it as a bounded crossover experiment while holding the original objective open.

`critic_jerk_bound.py` independently recovered the PM's necessary bound from zero physical initial x/v/a. Since x(t)=integral_0^t (t-s)^2 j_actual(s)/2 ds <= J t^3/6, tracking requires J>=6(q(t)-epsilon)/t^3. A small exact rational time search strengthened the bound to J>=60499239/6083500=9.944807923... at t=23/80, where q=20268813/512000000. This single-time witness is sufficient for a necessary bound; no optimality or attainability is claimed. Changes to the tolerance and initial acceleration were distinguished. The integral argument is hand mathematics plus exact Python arithmetic, not a Lean proof.

Independently checked the PM's continuous tracking bound for the alternative gain1/960. With z'=20(j-z), z(0)=0, |j|<=10 implies |z|<=10. Error satisfies `(D+40)^3 e=-j/6+z/12+80w`, with e/e'/e'' initially0. Its nonnegative impulse kernel t^2 exp(-40t)/2 has integral1/64000. For any measurable bounded |w|<=0.01, this gives |e|<=(10/6+10/12+0.8)/64000=33/640000 m=0.0515625 mm. Direct control similarly has bound37/960000 m. These are analytic all-time tracking bounds at fixed plant rate80 and exact measured-state feedback. They do not prove rate robustness, actual-jerk improvement, TV improvement, sensor-noise robustness, saturation safety, or physical usefulness. Reference joins preserve the required initial/continuity assumptions. The inference remains conditional on the recovered plant/controller contract.

The six additional co-design cases were subsequently independently reproduced, bringing the domain replay to11 laws and33,110 rows. Maximum new-case discrepancy was4.7e-12. They meet sampled tracking but their peak jerks12.1285–12.3256 and command variations9.6741–9.7198 exceed direct10.4834 and9.6314. Matching every u row also binds their discrete TV calculation.

For the nominal-inverse repeated-pole case, independently derived the domain researcher's closed form at r80,w0.01, zero initial physical/filter states: `(D+25)^4 e=16`, e/e'/e''0 and e'''0=-46/5. With c=16/390625, `e=c[1-exp(-25t)S3(25t)]-(23/15)t^3 exp(-25t)`. Its derivative simplifies to `exp(-25t)t^2(41t-23/5)`, so the unique positive minimum occurs at23/205. This hand check verifies formula and critical-time binding; the domain worker owns its rational exponential enclosure. It is a nominal tracking result, not a jerk/TV improvement or disturbance uncertainty proof.

`critic_bernstein.py` independently consumed the inventor's64 subinterval jerk certificates, expanded Bernstein bases back into power coefficients, checked exact equality to three derivatives of source q and complete interval coverage, and verified every Bernstein coefficient lies in[-10,10]. It rejected an in-range wrong coefficient, a coverage gap, and an out-of-range coefficient. This binds |j|<=10 for the positive-kernel tracking proof to the original source. It does not formalize convolution/ODE semantics in Lean.

### Robustness screen independently reproduced

`critic_robustness.py` independently reproduced all18 refined physical integrations at rates80/100/120 and disturbances-0.01/0/+0.01, direct versus fixed relocated gain1/960, with maximum metric discrepancy5.34e-11. All nine points have sampled tracking success and reduced command TV and integrated squared actual jerk. Peak jerk worsens at(80,-0.01) and(100,-0.01), is unchanged at several startup-limited points, and improves slightly at the two other nominal-rate points. Thus a uniform peak-jerk benefit is already refuted by this screen. Nine discrete points do not constitute a continuous rate/disturbance guarantee; no physical experiment occurred.

`critic_nominal_jerk.py` independently derived the nominal co-design jerk witness at t=1/20, when reference j=10. Error third derivative there is (2157/320)exp(-5/4). A rational positive-series upper bound for exp(5/4), including a geometric remainder, yields actual jerk>6932566030426/581044120585=11.931221373...>11.9. This is an exact one-time lower bound plus the previously checked closed-form ODE derivation. It does not itself certify the continuous peak of direct control. All nine critic Python scripts pass scoped Ruff checks.

### Analytic separation from direct peak jerk

A later direct bound closes the limitation above for the repeated-pole nominal co-design. Independently derived the reference-to-actual-jerk transfer `G(s)=1-s^3/[6(s+40)^3]`, using zero e/e'/e'' initial values. Its impulse measure is a5/6 feedthrough plus continuous kernel `(40/6)exp(-x)(3-3x+x^2/2)`, x=40t. The polynomial has roots3±sqrt3. Its antiderivative is `-exp(-x)(x^2/2-2x+1)/6`; hence its negative area is `N=[(sqrt3-1)exp(sqrt3-3)+(sqrt3+1)exp(-3-sqrt3)]/6`, and total absolute impulse mass is1+2N because total signed mass is1.

The constant-disturbance contribution is0.8 exp(-x)(1-2x+x^2/2). Its only positive critical points are the same roots3±sqrt3, with values(1±sqrt3)exp(-3∓sqrt3), all of magnitude below1; its initial value is1 and its limiting value0. Therefore the disturbance contribution has magnitude at most0.8. Nonzero initial reference jerk10 is allowed: q/q'/q'' and error e/e'/e'' are zero, so the causal convolution initial terms are correct.

`critic_direct_bound.py` independently verifies the primitive/root identities and rational exponential inequalities. They give N<343/7680 and direct global absolute actual jerk<22451/1920=11.6932292. The independent co-design witness at t=1/20 exceeds11.931221373. Thus the nominal repeated-pole co-design has a strictly worse actual-jerk peak than direct, analytically, not just on a sampled grid. This combines hand ODE/convolution reasoning, an independently checked source-jerk certificate, and exact rational arithmetic; it remains outside the Lean kernel. The bound applies to the recovered constant-disturbance nominal task, not arbitrary plant uncertainty. Ten critic Python scripts pass scoped Ruff lint and formatting checks.
