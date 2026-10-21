# C09 — active source separation with retained dynamics

AI-written inventor review; inherited exact model identifier unavailable. Root owns the600-second session and PM decision. Originals were read only. Own artifacts are two scripts and their JSON outputs.

The useful path is to bind a source-separating experiment to a causal observation operator and a full intervention/termination envelope. A finite-window displacement demodulator needs retained-state boundary terms. A frequency or phase change also needs an explicit bound on how much the nuisance source changes during the experiment.

## Source boundary

Read the frozen card and the original `adjacency-review/coupled-measurements.txt`, `source-attribution/challenge.txt`, and `source-attribution/model.json` under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/`.

The original model is signed, scalar, static, with wheel gain1 and invariant sources/transfers. Its wheel residual limit is1/8 and mixed-response limit3/4. Its trial mass is not an independent attribution row. Prior w,d lie in[-2,2]. None of these establish oscillator damping, a force-to-readout map, controllable phase, or actuator safety. The following dynamical and phase-control models are explicitly new diagnostic contracts.

The existing source review cites [SAE2005-01-2307](https://doi.org/10.4271/2005-01-2307) for relative roll-speed separation. My fresh publisher-page fetch timed out; I did not read or claim access to its full paper. The transfers below are derived here, with no novelty claim.

## Transfer1: finite-window lock-in as a boundary-preserving operator

Map the ideal source demodulation to the actual dynamical readout before updating the feasible source set. The pod separately examines frequency-offset leakage; my contribution is the state-dependent observation interface.

For the declared oscillator `x''+2a x'+a²x=f`, constant a, define `Xomega=(1/T)int_0^T x(t)e^(-i omega t)dt`, and similarly Fomega. Integration by parts gives exactly

`Fomega=(a+i omega)^2 Xomega + ([v e^(-i omega t)]_0^T +(2a+i omega)[x e^(-i omega t)]_0^T)/T`.

This preserves the complete finite-window dynamics, including the starting state and the terminal state. It does not require numerically differentiating the whole noisy displacement record, but it does require certified endpoint velocity/position information or a valid outer bound. Unknown a must remain in the same joint feasible set as the endpoint states and source parameters.

Falsifier: free decay `x=e^(-at)`, with f=0, gives a nonzero naive inverse-transfer demodulation. The boundary term cancels it exactly. Thus even a source-free inherited transient can be falsely attributed if the steady-state transfer is applied to a finite record. `inventor_boundary.py` checks36 Gaussian-rational substitutions of the resulting algebraic identity. The exponential endpoint is treated as a formal variable; the rational substitutions are not claimed to be actual exponential values. The continuous identity is a hand integration-by-parts derivation, not a kernel proof.

A causal decision can use data only after this window and its required endpoint observations arrive. Data latency and the transition to the next action must remain inside the safety envelope. Changing normalization from analytic complex signals to real-cosine demodulation requires accounting for the conjugate-frequency term; no unmentioned factor2 is assumed here.

## Transfer2: positive-system envelopes / retained energy and safe termination

Use a declared normalized family of critically damped support models:

`x''+2a x'+a²x=f`, constant `a in[1,2]`, `|f|<=4`.

The force limit follows only under the newly declared interface `f=w cos(theta_w)+d cos(theta_d)`, with both source amplitudes bounded by2 throughout the intervention. It is not inferred for speed-squared physical imbalance under arbitrary speed changes. Added transition forces, drive torque, and support changes need their own bounds.

Set `y=v+a x`. Then `x'=y−a x`, `y'=−a y+f`. Retain initial states satisfying `|x0|<=1`, `|v0+a x0|<=1`. The rectangle

`|x|<=4/a²`, `|y|<=4/a`

is invariant: at each positive boundary the worst outward derivative is zero, and likewise at the negative boundaries. Hence all intervention waveforms satisfying the force interface stay within displacement4 and velocity8. The bounds are nondimensional diagnostic limits, not the original stopping tube and not measured vehicle limits. The a-dependent initial relation is a joint condition, not permission to reset y or pick a favorable parameter.

During a declared spin-down interval, the same bound continues if the total forcing remains bounded by4. Only after both source forces actually vanish at Toff does the free-decay formula apply. Retaining the terminal state gives

`|x(Toff+s)| <= (4/a²+4s/a)e^(-a s) <=4(1+s)e^(-s)`.

At s=6, a positive Taylor lower bound `e^6>2587/7` yields the exact upper bound `196/2587<1/10`. This envelope decreases thereafter. No instantaneous mechanical stop, state reset, or finite damping-independent settling guarantee is assumed. `inventor_intervention.py` checks the boundary algebra and rational exponential bound; continuous invariance/comparison is hand-derived.

Falsifiers: the changed diagnostic undamped plant `x''+x=cos t`, initially at rest, has `x=t sin(t)/2`. At3pi/2, displacement magnitude3pi/4 exceeds1. At a window endingT=2pi, position is0 but velocity ispi. Turning off the force then produces a free oscillation of amplitudepi. Endpoint position alone therefore cannot certify the termination. These examples do not refute the stated critically damped family; they identify why damping/state hypotheses are essential.

Timing obstruction: a one-turn demodulation null with relative-frequency authority `Delta<=1/10` requires `T=2pi/Delta>=20pi>60`. It is invalid to combine that leakage argument with a shorter safe-time authorization. This is necessary for that particular cancellation protocol, not a universal lower bound for every estimator.

## Transfer3 (unexpected): ABBA phase cycling as a drift-rejecting experiment

Declare an alternative intervention with actual controlled wheel phase signs `s=(+1,−1,−1,+1)`, equally spaced equal-width readout windows, constant wheel amplitude w, and an unchanged calibrated transfer. The window observations obey `z_k=s_k w+average(d)_k+e_k`. This is not supplied by a trial-mass sensitivity test; relative phase authority and transition gaps must be established.

The estimator `what=sum(s_k z_k)/4` cancels constant and affine nuisance drift. It does not gain a factor2 in deterministic bounded noise: if each error is bounded by epsilon, the exact worst-case error remains epsilon, attained by `e_k=epsilon s_k`. If `|d''|<=L` and center spacing is tau, the nuisance bias is bounded by `L tau²/2`. The second-difference identity proves this, and a quadratic nuisance attains it. Equal finite windows preserve that bound by averaging the same shifted identity.

Under the original wheel tolerance1/8 and epsilon1/40, this bound requires `L tau²<=1/5`. Relative phase-rate authority at most.1 requires a pi phase transition to last at least10pi. Thus making the intervention gentler can worsen attribution by leaving more time for nuisance drift. This is a real information/safety tradeoff for the declared protocol, not a generic claim that longer data are worse.

An exact finite-window negative control uses width1/2, center spacing32, and the smooth nuisance

`d(t)=1/2+((t−48)^2−48^2−(1/2)^2/12)/2000`.

On the whole observation span[-1/4,96+1/4], d remains within[-2,2], and `d''=1/1000`. Gaps31.5 suffice for a pi phase change with relative rate below.1 using pi<22/7. With truew=1/2, the first window average retains the original baseline1. The four nuisance window averages are `1/2,−131/250,−131/250,1/2`. The ABBA estimate is `253/250=1.012`, although truew=.5.

An unchanged-nuisance consumer using epsilon1/40 would accept correction−1 for the wheel test, since `.012+.025<.125`. The actual wheel residual is.5 and violates the criterion. A drift-aware consumer instead keeps error bound `537/1000` and refuses. This does **not** invalidate the original static certificate: the example deliberately changes its source-amplitude-invariance assumption. It shows why an intervention must justify that assumption rather than inherit it silently.

The phase transition construction constrains phase velocity only; it supplies no phase acceleration/torque bound. This exact test uses ideal calibrated source-equivalent window readings. The oscillator-to-readout boundary contract above is the proposed bridge, not an already integrated sensor implementation.

## PM recommendation and evidence

GO for a bounded joint experiment certificate that includes: admissible relative-frequency/phase history, the source/transfer drift budget, the finite-window observation boundary terms, retained plant state, and a safe termination schedule. HOLD physical instantiation until support/damping, phase authority, source speed-scaling, endpoint sensing, and actuation/latency bounds are named and justified.

Do not promote source attribution based only on static separating rows, steady-state transfer inversion, or terminal displacement. Do not treat a current noise interval as statistically independent across the four windows.

Both own exact scripts pass. Ruff check/format are required on the final versions. No Lean, solver, hardware, general uncertain oscillator, or vehicle validation is claimed. The positive oscillator bound is deliberately conservative and is not necessary for safety.

Quality rubric: source binding4/5, mechanisms4/4, discriminating tests5/5, independent-check readiness3/3, scope discipline3/3 =19/20. Subjective confidence in the algebraic findings95%; no probability is assigned to feasibility on the user's physical mechanism.

## Supplement: root's closed two-axis force-sensor toy interface

The PM selected an explicit **direct two-axis force sensor**, encoded as a complex measurement. This is a different sensor interface from displacement demodulation. The boundary correction in Transfer1 remains a useful negative for a displacement-sensor implementation, but is not needed for the PM's ideal direct-force measurement. This choice closes a declared toy model; it does not establish that such a calibrated sensor exists on the user's mechanism.

Extend the support model to complex x,v,f with the same real, constant a in[1,2]. Variation of constants has positive real kernels, so the scalar norm bounds carry over:

`y(s)=e^(-as)y0+int_0^s e^(-a(s-r)) f(r)dr`,

`x(s)=e^(-as)(x0+s y0)+int_0^s (s-r)e^(-a(s-r)) f(r)dr`.

The phase-detuning and transition stages obey |f|<=4 under the explicit bounded source-force interface. Retain their actual terminal state; there is no reset. The predeclared center z=1/2 and correction c=−1/2, with the pod's joint bounds `|w−z|<=123/3920`, `|d|<=495/784`, imply the arbitrary-relative-phase post-correction force bound

`Fpost =123/3920+495/784=1299/1960<3/4`.

For a ramp gamma in[0,1] that implements the corresponding convex combination of old and corrected forces at the current phases, `|f_gamma|<=(1−gamma)4+gamma Fpost<=4`. This is a pointwise force-interface guarantee; no phase acceleration, motor torque, or lag guarantee is being inferred from it.

At the end of that ramp, use the retained coarse bounds |x0|<=4, |y0|<=4. For all s>=0 and a>=1, comparison of the positive kernels with their a=1 values gives

`|y(s)|<=Fpost+(4−Fpost)e^(-s)`,

`|x(s)|<=Fpost+(4−Fpost)(1+s)e^(-s)`.

For example, the x bound follows from

`4(1+s)e^(-s)+Fpost int_0^s u e^(-u)du`.

The formula is monotone decreasing from4 toward Fpost. It accounts for inherited transient motion while arbitrary bounded post-correction forcing continues. At s=6, the exact exponential lower bound gives `|x|<1840511/2535260<3/4`. The normalized displacement threshold here is a separate diagnostic quantity; numerical equality with the static force threshold does not establish equal physical units.

Returning relative frequency to zero ends the separating excitation but need not remove the sources. Thus this termination is **continued safe bounded forcing, not rest**. A permissible sustained harmonic force at a=1, omega=1 has a particular response with nonzero displacement amplitude `Fpost/2=1299/3920`; its motion persists. The force-removal tail in Transfer2 is optional and applies only when its stronger hypothesis actually holds.

`inventor_closed_interface.py/json` checks the exact joint force budget, convex ramp bounds, and rational post-handoff bounds. The general complex ODE comparison is the hand argument above, not a Lean trajectory theorem. Physical direct-force sensing, relative-phase actuation, source amplitude/speed-squared scaling, and torque/lag interfaces remain HOLD items. The final three inventor scripts pass Ruff check and format.
