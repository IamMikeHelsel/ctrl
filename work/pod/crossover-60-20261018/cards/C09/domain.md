# C09 domain: finite-window separation with explicit phase and noise contracts

AI-generated domain research; inherited model, exact runtime identifier unavailable. Original sources/model unchanged. This review derives a proposed separating row; it does not claim the original synthetic leakage interval[1/5,3/10] follows from a physical experiment.

The [official SAE2005-01-2307 abstract](https://saemobilus.sae.org/papers/driveline-imbalance-sensitivity-testing-methodology-2005-01-2307) describes overlapping orders and separation through small differential roll-speed adjustments on a chassis dynamometer. Only the abstract/metadata were inspected. The established method motivates this toy; no vehicle procedure, hardware capability or new attribution method is inferred.

## Source binding

The original fixed model is real and single-phase. It assumes wheel gain1, priors w,d in[-2,2], q=lambda*d with lambda in[.2,.3], baseline w+d observed1 with error.1, and a separating w+q row observed5/8 with error1/40. Its trial is redundant because gain1 is already assumed. Its held-out leakage is exactly half the same lambda by assumption. Those rows and the prior interval remain untouched.

Our new complex measurement model instead uses a derived small complex leakage disk and a different readout z=1/2. It does not reproduce the original separating observation5/8. Complex norm errors are not interchangeable with coordinatewise signed error bars or covariance bounds. The finite-window dynamics below distinguish C09 from the prior S12 static uncertainty/action exercise.

## Declared demodulation experiment

For t in[0,T], assume an analytic complex/IQ response

y(t)=w exp(i*omega_w*t)+d exp(i*omega_d*t)+e(t).

Unknown constant initial phase is absorbed in complex d. Both amplitudes and transfer paths are constant over the window; omega_w is exactly tracked and both frequencies are constant. Suppose the pointwise complex error obeys |e(t)|≤E. Wheel-synchronous rectangular demodulation gives

z=(1/T) integral_0^T y(t) exp(−i*omega_w*t)dt
 =w+L*d+epsilon,

L=exp(i*Deltaomega*T/2) sin(Deltaomega*T/2)/(Deltaomega*T/2), |epsilon|≤E.

This integral identity and its deterministic error estimate are hand-derived; the existing Lean module begins at the displayed scalar sinc expression. No independent-noise or square-root averaging claim is used.

Choose Deltaomega_nom*T=2*pi and Deltaomega=(1+delta)Deltaomega_nom, with |delta|≤eta<1. Then

|L|=|sin(pi*delta)|/[pi*(1+delta)]≤eta/(1−eta).

For eta=.01, |L|≤1/99. Constant unknown phase does not affect the norm bound. This derivation does not cover arbitrary time-varying frequency/phase, changing amplitudes or support transfer, uncertain wheel demodulation frequency, or an unmodeled analytic-signal filter. With no separation, L=1 and source ambiguity remains.

A bounded relative-speed intervention also has a timing requirement: if admissible offset is at mostOmega and stationarity is guaranteed only forTmax, a nominal full beat requires Omega*Tmax≥2*pi. The existence of such a safe offset, and the transient while reaching/returning from it, are unproved plant contracts. More complete nominal beats do not improve the simple eta/(1−eta) bound and accumulate more terminal phase error.

## Quadrature and real-sensor boundary

An observation of only the real part of z cannot certify a full imbalance norm. The two worlds w=.5,d=.5 and w=.5+i,d=.5−i have the same complex baseline1 and the same real separated readout.5 when L=0; after correction−.5 the second wheel residual has norm1. Its source norms still satisfy the bound2.

A real sensor followed by2/T complex demodulation is a different measurement model:

z=w+conj(w)L(−2omega_w)+dL(Deltaomega)+conj(d)L(−omega_d−omega_w)+epsilon.

If omega_w*T=2*pi*N exactly, the wheel image vanishes. With one nominal relative beat, nuisance leakage is bounded by

eta/(1−eta)+eta/(2N+1−eta).

A pointwise real sensor errorE gives the conservative demodulation error2E, notE. For N=10, eta=.01, E=1/40 and |d|≤2, the resulting wheel-error budget remains below1/8, but this is a separately declared real-sensor version. Merely calling a real measurement 'complex amplitude' does not remove its image terms or provide an unobserved quadrature.

## Measurement-to-action bridge and the phase correction

Use retained joint constraints b=w+d+e0 and z=w+Ld+e1, with |e0|≤1/10, |e1|≤1/40, |L|≤1/99 and initially |d|≤2. Correction c=−z gives wheel residual at most179/3960<1/8. At fixed nuisance phase, the mixed residual for real rho in[0,1] interpolates between w−z and b−z−e0. For b=1,z=.5 its bound is.6.

Returning to the original frequency does NOT automatically restore nuisance phase. The one-beat constant-detuning model leaves a relative factor exp(i*2*pi*delta). A phase-chord bound adds at most2*pi*.01*2≤22/175, giving127/175<.75. This optional path requires the stated phase-evolution contract; more beats can worsen it.

A stronger joint bound avoids requiring any terminal phase closure. Let x=|w−z|, D=|d|, K=|b−z|+.1. The same retained variables satisfy

x≤epsilon+ell*D, D≤K+x.

Therefore x≤B=(epsilon+ell*K)/(1−ell) and D≤K+B. With ell=1/99, epsilon=1/40, K=3/5,

B=123/3920<1/8,
D≤495/784,
|w−z+transfer*d|≤B+D=1299/1960<3/4

for every complex transfer with norm≤1, including arbitrary nuisance phase. This keeps wheel reference phase and nuisance magnitude unchanged, but not nuisance angle. It is a sound conservative bound; no claim of sharpness for the actual sinc response is made.

The exact negative fixture w=19/40,d=5/8,L=0,e0=−1/10,e1=1/40 fits b=1,z=.5. Changing nuisance phase by−1 gives mixed residual13/20>.6. The new phase-free bound covers it. Thus the former fixed-phase.6 certificate must not be reused after an unspecified phase change.

## Evidence and acceptance

`domain_demod.lean`2 declarations prove the sinc inequality and one-percent specialization. `domain_complex.lean`5 prove complex measurement residual and convex interpolation bounds. `domain_phase.lean`4 prove the complex phase-chord bound and optional one-beat budgets. `domain_feedback.lean`3 prove the joint fixed-point bound, arbitrary complex-transfer norm bound and rational constants. All14 compile exit0 with permitted axioms only. Failed first drafting logs are retained; their missing/invalid proofs are not accepted. Independent critic replay is a separate gate.

`domain_exact_cases.py/json` uses exact rational two-coordinate complex fixtures to check the quadrature failure, phase-change counterexample, joint bound and real-sensor budget. Scoped Ruff checks pass. The analytic integral identity, physical source/transfer invariance, full intervention safety and actuator realization of a complex correction remain outside these kernel statements.

Suggested decision: GO for the explicit demodulation-to-retained-set experiment and its falsification tests; HOLD a physical safe-excitation claim until offset authority, transient safety, source invariance and sensing contracts exist. Precise next test: use a declared dynamic source/transfer model and recorded phase trajectory, retain wheel/drivetrain/error tuples through the full intervention and safe return, then challenge the leakage bound under frequency drift and real-sensor image terms. Quality grade4/5 for this bounded analytical gate; subjective confidence high in the compiled statements, with no hardware or novelty claim.
