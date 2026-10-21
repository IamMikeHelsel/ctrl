# C09 independent critique

AI-generated review; inherited model, exact identifier unavailable. Original files preserved. This review addresses generating useful information through a bounded intervention, rather than repeating S12's static feasible-set adapter.

## Source binding

The original source-attribution model is a real, signed-phase static example. Wheel gain one, leakage in [1/5,3/10], unchanged source amplitudes and support paths, and a held-out row with exactly half the same leakage are assumptions. The new complex one-beat demodulation experiment replaces those measurement assumptions; it does not derive the original leakage interval or half-leakage relation.

The official [SAE 2005-01-2307 abstract](https://saemobilus.sae.org/papers/driveline-imbalance-sensitivity-testing-methodology-2005-01-2307) was independently recovered through publisher search after direct fetch timed out. It supports differential wheel-roll-speed order separation on a chassis dynamometer as existing prior art. It does not supply the proposed robot's actuation, transfer calibration, safety envelope or termination mechanism. Only the abstract was reviewed.

## Independent accepted algebra

For b=w+d+e0 and z=w+L*d+e1 with complex norms, |e0|<=.1, |e1|<=.025, |L|<=1/99 and prior |d|<=2, the wheel bound179/3960 is valid. Interpolating rho in[0,1] between wheel and baseline endpoints gives mixed bound .6 for b1,z.5 when nuisance phase remains fixed.

A better route retains the shared nuisance variable. Set K=|b-z|+.1=.6 and x=|w-z|. Then x<=.025+ell*D and D<=K+x imply x<=(.025+ell*K)/(1-ell). With ell1/99, x<=123/3920 and D<=495/784. For any final complex nuisance transfer of norm at most one, the mixed residual is at most1299/1960≈.662755. This covers arbitrary nuisance phase, provided its magnitude and the wheel phase/transfer remain bound. It avoids requiring perfect phase closure or discarding uncertainty shared by the measurements.

`critic_joint.py/json` independently consumes the PM fixture, verifies the reconstructed witness and all bounds, and rejects four corruptions (bound, leakage witness, observation, correction). The witness attains the bound in the abstract complex leakage disk; the sinc locus need not attain its outer radius. The sufficient relative-frequency-error threshold2/29 applies to this disk bound, not an optimal physical experiment. Earlier prior-only and one-pass posterior bounds remain valid but looser.

The sinc inequality uses a constant relative detuning and actual window with nominal one beat. Domain's integral-to-sinc identification is an analytic bridge, not yet kernel checked. Joint +1% frequency and +1% window-duration errors produce effective detuning201/10000; an elementary sine lower bound gives leakage greater than1/99. Thus the sampling clock is part of the contract. A phase-closure correction127/175 is valid but unnecessary for this example after the phase-independent joint tightening.

## Independent failure cases and intervention audit

- Discarded quadrature: w=.5+.25i,d=.5-.25i reproduces all original real projected readings, but correction-.5 leaves wheel norm.25, above.125. This is a complex extension countermodel, not a refutation of the explicitly real original model.
- A common pi rotation of both readouts can preserve the numeric admission bound while an untransported correction doubles the actual wheel residual. The actuator and measurement phase references must be connected.
- Wheel source drift .2 after observation makes the old correction fail. No-drift or a quantitative drift budget is required; unchanged measurements are not evidence about a later changed source.
- Real sensing is not analytic complex sensing. With T1, omega_w=pi/2, omega_d=5pi/2,w=d=.5, the analytic demodulated nuisance cancels, but doubled real-force demodulation gives .5-4i/(3pi). The image error exceeds14/33, far above.025. A quadrature channel or explicit image-term bounds are required.
- For the oscillator family, displacement gain is H_a(i omega)=1/(a+i omega)^2, not one. Unknown a and finite-window endpoint terms cannot be silently removed. Two integrations by parts give Fomega=(a+iomega)^2 Xomega+([v exp(-iomega t)]+(2a+iomega)[x exp(-iomega t)])/T. The identity does not estimate a or bound noisy endpoint data by itself.

The inventor's finite ABBA counterexample independently reconstructs exact window means(.5,-.524,-.524,.5), wrong wheel estimate253/250, and drift-aware error537/1000. The smooth nuisance remains bounded and the phase-transition intervals are explicit. Thus a known phase pattern alone cannot distinguish a drifting nuisance without a drift model. No deterministic independent-noise averaging gain is available.

The critically damped family x''+2a x'+a²x=f, constant a in[1,2], |f|<=4 admits the declared retained-state rectangle through z=v+a*x: |x|<=4/a², |z|<=4/a. The independent homogeneous-tail derivation gives |x(Toff+s)|<=4(1+s)exp(-s) after actual f becomes zero, and at s6 the rational bound196/2587<.1. This is a separate synthetic dynamic contract with an explicit comparison argument, not the static model's vibration threshold. Stopping a detuning command does not remove wheel/drivetrain forcing: a1,f4,x4,v0 is a nondecaying equilibrium. Source removal, spin-down forces, correction application, sensor interfaces and acquisition ramps are unproved.

## Prospective dynamic variant supplement

The PM subsequently declared a separate direct two-axis force sensor and speed-squared nuisance forcing. Baseline speed10, nominal detune.1 with constant relative gain error1%, ten-unit ramps and a one-beat plateau give gain maximum1.02030201 and probe force4.04060402. Independent `critic_speed.py/json` reproduces the effective leakage, updated wheel/mixed posterior, and all exact budgets. Post-correction force is bounded by approximately.663016753 for arbitrary nuisance phase. Under the stated constant-a oscillator, positive-kernel comparison from the retained state gives position at most.722124531 after six further time units, and thereafter. This permits continuing forcing and does not claim rest.

This supplement closes the algebraic toy interface only by declaring direct vector-force sensing, ideal bounded relative-speed tracking, unchanged wheel reference/path, and a physical correction coefficient actuator. It does not derive those capabilities from displacement data or a robot. The travel limits4.1 during probing and1 after the settling interval are explicitly prospective diagnostic choices, not historical predeclared criteria. The bound20+20pi<83 covers detune ramps, acquisition plateau and return. The final supplement supplies a one-second correction c(s)=-.5(10s³-15s⁴+6s⁵), s in[0,1], held constant afterward. Independently checked monotonicity and derivative bounds give amplitude at most.5 and slew at most15/16. Thus the complete conditional toy timing, including six further settling units, is27+20pi<629/7<90. This resolves the initial missing-duration caveat; it requires the declared force-phasor actuator and is not an intervention that attaches a mass to a moving wheel. No jerk limit is claimed.

The final half-beat negative independently verifies a failure of certificate reuse: Deltaomega*T=pi gives L=2i/pi, w=.5,d=.25,b=.75,z=.5+i/(2pi). The incorrect one-beat gate produces wheel bound below577/19600 and mixed bound below919/1960, yet actual wheel residual1/(2pi) exceeds.125. This changes only the acquisition window within the complex analytic model, so exact clock/phase-product binding is load-bearing. `critic_final.py/json` also rejects extrapolating the correction polynomial outside its interval and compressing the ramp to half a second.

## Evidence and gate

Exact rational scripts and independent producer consumers are in critic_exact, critic_intervention, critic_joint, critic_speed and critic_final. All14 frozen Lean declarations independently compile successfully with only permitted axioms; counts and hashes are recorded in critic_acceptance.json. Their scope is sinc bounds, complex norm estimates, shared-error algebra and phase bounds, not a complete safe excitation or oscillator execution theorem.

GO for a typed acquisition-to-action contract that preserves the complex uncertainty and uses the joint fixed-point bound. HOLD an end-to-end claim that bounded excitation safely generates this measurement and safely terminates on a physical robot. The next discriminating experiment must connect actual measured displacement/force and retained endpoint state to the demodulated complex reading, then prove the excitation and termination envelopes under the same plant and source tuple. Empty feasible sets must block action, and correction actuation needs its own force/rate authority.

Quality18/20: source binding5/5, independent algebra5/5, failure cases5/5, end-to-end realization3/5. Subjective confidence high in the stated algebra, unresolved in acquisition/actuation realization. No probability of practical success is asserted.
