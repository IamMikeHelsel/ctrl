# R11 independent critique

GO for a typed frame/jet, timestamp and authority contract; HOLD a physical or fully composed multirate gaze guarantee. The frozen source is explicitly preparatory research with no controller or hardware result. The new scalar rates, delays and tolerances are declared toy parameters, not measurements from the source robot.

## Source scope

The [CTU project description](https://aa4cc.dce.fel.cvut.cz/archiv/content/inertial-stabilization-and-visual-servoing-aerial-surveilance.html) documents inertial line-of-sight stabilization with tracking layered above it. The [institutional dissertation summary](https://wiki.control.fel.cvut.cz/mediawiki/images/2/23/Diz_45_TEZE.pdf) identifies low camera sampling rates and approximately one sampling-period delay as an engineering issue. This corroborates the proposed decomposition as prior work; it does not validate this campaign's toy gains. Full dissertation retrieval through the web tool exceeded its size limit, and PubMed supplied no usable pigeon abstract during this review. No new biological mechanism or IMAX claim is accepted.

## Algebraic cancellation versus actual output

For the declared first-order relative-angle actuator qdot=a(c−q)+w and world angle beta+q, desired relative position r−beta is only a kinematic target. Without rate feedforward, world tracking error obeys edot=−a e+(betadot−rdot)+w. A constant base ramp therefore leaves a nonzero lag. Matched inverse feedforward cancels the rate term, but nominal actuator mismatch leaves (1−a/a_nom)(betadot−rdot). Stale base angle and rate must be bound at their actual timestamp and in the same frame.

Independent exact tests show a base ramp at1rad/s with actuator rate10/s has world error greater than.05rad at.1s under position-only cancellation. A20ms stale angle with constant-rate feedforward still leaves nonzero error and asymptotic bias.02rad. These are separate diagnostic parameters, not the domain's40/s sampled experiment.

The domain experiment was independently reproduced by propagating the physical q state with directed70-digit fixed-point intervals and a positive exponential series/inversion. The producer instead used an alternating exponential enclosure and a closed error recurrence. At.082s, from the same retained q=−.002 at.002s, the three errors are approximately:

- coordinated feedforward:.002401291864rad;
- omitted rate feedforward:.026382236765rad;
- wrong rate sign:.050363181665rad.

The first critic harness used floating division while constructing the scaled initial integer. That draft and output are preserved and excluded; exact integer initialization was restored and the entire replay rerun before acceptance. No conclusion changed.

The declared3ms smooth-command budget gives7/1600rad<.005rad. Its control-rate budget1.465rad/s must be distinguished from actual joint rate, which includes disturbance and is bounded by1.475rad/s. Joint travel, position command range, torque and coupled inertia are not covered. Unbounded base ramp cannot be claimed within finite travel limits.

## Sensor blackout and retained state

Two base motions beta±(t)=±A t²/2 share initial angle/rate. If all available data remain identical and the independent actuator evolves identically during a blackout, its endpoint q is common. Then max(|q+Ah²/2|,|q−Ah²/2|)≥Ah²/2, with equality atq=0. At A=2rad/s² andh=.02s this is.0004rad, exceeding the hypothetical.0001rad target. Six small critic lemmas kernel-check the endpoint inequality, sharpness, numeric budget and scalar error identities. They do not establish the causal/data premise for a real gimbal; fresh world-gaze measurements or base-coupled actuator information can invalidate that premise.

For the outer loop, every saved row was independently checked against x[n+1]=x[n]−kappa*x[n−1] with retained delayed state. The exact energy x²−xy+kappa*y² scales bykappa. Atkappa=6/5 the speed contract is first violated atn=6,t=.12s; subsequent linear traces are not certified clipped-plant behavior. Atkappa=1/2 the100-step maximum command is1/40rad/s. Changing sample time, retained error, speed command or energy in the receipt is detected. The delay-free surrogate contracts at the unstable delayed gain, so silently dropping the delayed state changes the conclusion.

## Composition boundary

The exact outer recurrence assumes matched fresh inner cancellation and zero inner error. A nonzero inner error eta enters visual feedback and adds−kappa*eta[n−1] to the recurrence. Moreover, the outer reference is continuous piecewise linear, with jumps in rdot, while the domain3ms age bound assumes bounded reference acceleration. The two positive results therefore cannot simply be combined into a5mrad overall target-tracking guarantee. Smoothing or jump-aware age bounds, an interconnection disturbance gain and a shared authority check are still required. Any step change in the world goal must retain actual actuator state and previous measurements; resetting error is a different trajectory.

The subsequent nominal ramp candidate repairs the acceleration discontinuity: it linearly interpolates velocity across each 20 ms interval, using two retained delayed errors. An independent rational consumer verified all 100 saved rows, the exact identity P−AᵀPA=I, and positive LDL factorizations of P−0.5I and 20I−P. Changing a matrix coefficient, delay coefficient, initial history or initial velocity is rejected. Its declared initial history gives a 1 mrad reference-error envelope, velocity at most 0.01 rad/s and acceleration at most 1 rad/s. The first retained velocity must already equal −0.001 rad/s; otherwise the first segment silently changes velocity. No jerk limit is proved. This is a nominal repaired reference generator, not yet a robust visual-feedback interconnection.

The sensor supplement gives a 4.6 mrad inner reference tube and a 1.484 rad/s actual-rate budget under its stated smooth-reference and sensor assumptions. Its inward-face inequalities are conditional field statements, not a global execution theorem. Adding the separate 1 mrad nominal outer envelope would give 5.6 mrad by a plain triangle bound, already above 5 mrad; moreover, that nominal outer envelope does not yet apply to feedback contaminated by the inner error. A tighter composition analysis or revised budget is necessary.

An exact directed-interval countermodel now makes the missing interconnection contract concrete. Start with the same three reference-error samples 0.0001 rad, zero inner error, and retained velocity −0.001 rad/s. Let eta obey eta′=−40 eta+f with piecewise constant |f|≤0.184, and drive the three-state delayed ramp using measured error y=x+eta. The serialized conditioning and reversal sequence in `critic_perturbed.json` yields y>0.00666702471342 rad at 2.16 s, while ramp acceleration stays below 0.923 rad/s² and speed below 0.067 rad/s. Each held inner flow is a convex combination of its initial eta and f/40, so |eta|≤0.0046 holds throughout, not only at samples. The ramp velocity is affine per interval, so endpoint speed and constant acceleration checks cover each interval. Root independently reproduced the corrected three-state trajectory at 90-digit precision.

This disproves a 5 mrad guarantee inferred from those aggregate contracts alone. It is not a physical realization of the specific timestamp and sensor channels: those may impose correlations absent from arbitrary f. The initial abrupt-conditioning draft violated the acceleration bound; a subsequent two-history draft used the wrong delayed recurrence. Both failed drafts and outputs are retained and excluded. The corrected version uses three retained reference and inner-error samples, with the two delayed measured outputs controlling each ramp. Actual visual error y is distinct from reference error x.

The inventor's constructive cubic Hermite prehistory also discharges kinematic startup consistency: two segments return to the same sample position with velocity −0.001 rad/s, while speed stays at most 0.001 and acceleration at most 0.3. This is a controller handoff history, not a history generated by the same outer controller. Target changes still require a separate retained-velocity and admission rule.

## Multi-axis transfer

The inventor's smooth noncommuting rotation paths were independently differentiated by product-rule recursion rather than its Taylor-series code. World and relative jets match through third order; relative third derivative is(0,−1,10). Omitting the centripetal acceleration term produces false world acceleratione1 for a stationary goal. A passive frame relabel that transports position but retains old velocity yields false world velocity(1,1,0). The five noncommutative Lean identities are algebraic reconstruction statements. Instantiation as actual smooth rotation derivatives, optical-ray versus joint mapping, singularities and actuator feasibility remain explicit obligations. A ray derivative is not automatically a gimbal joint velocity or torque.

A constructive alternative is to admit residual increments, not amplitude alone. In measured-output coordinates Y=(y_k,y_(k−1),y_(k−2)), the same matrix A receives u=eta_(k+1)−eta_k in its first coordinate. Independent matrix algebra gives C=AᵀPe1=(1515/158,−165/79,−357/316); Young's inequality yields V_next≤(39/40)V+207u². Initial V≤5e−7 and |u|≤5e−6 make that energy bound invariant and imply |y|≤1 mrad. The three scalar arithmetic and conditional admission lemmas independently kernel-replay; the matrix/Young inequality and induction are hand derivations. This is an informative prospective admission condition, not something supplied by the existing age and sensor amplitude bounds. Visual measurement bias must also enter the appropriate state and increment channel.

## Independent formal acceptance

45 printed declarations independently compile with only propext, Classical.choice and Quot.sound: critic blackout 6, domain scalar 7, domain sensors 4, inventor transport 5, root delayed outer 9, root smooth ramp 7 and root feedback identities 4 and domain increment admission 3. Hashes and logs are recorded in `critic_acceptance.json`. These are explicitly scoped algebraic and conditional bounds; they are not a full physical interconnection or ODE execution proof.

## Gate

Next block after breadth: implement one frame/version/timestamp-bound command consumer, preserve the complete relative jet and delayed outer state, and execute the twenty semantic mutations in `critic_next_gate.json`. Separate the ideal continuous outer-loop experiment from the finite-age bounded-acceleration servo contract until a composition proof is supplied.

Quality17/20. Confidence is subjective and high for these exact toy counterexamples and replays; no calibrated success probability or physical acceptance is claimed. Original sources and approved challenges were not changed.
