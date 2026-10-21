# C10 inventor — finite-time certificates expose a rate-quantifier obstruction

AI-written inventor role; inherited root model, exact identifier unavailable. PM owns session timing and decision. Read frozen CARD, tracking-replans README/comparison.py/results, and filter-enclosure-08 report. Originals remain unchanged; no simulation installation or hardware work.

The original short profile has jerk `(10,−10,−10,10)`m/s3, four phases of1/50s, then4s hold. Its endpoint is1/6250m=0.16mm and total horizon4.08s. The slow plant uses sigma1 and r∈[8,12]. Existing controllers use kappa0,1/10,5/48; none is silently substituted for another. The source's previous four rate signals are a finite test set, not the entire admitted time-varying family.

## Transfer 1 — finite reachability as a decisive acceptance and rejection instrument

Map the exact piecewise-linear error ODE to a finite-dimensional autonomous system, preserving physical/error state at joins. For constant jerk and rate on each phase, append a constant coordinate. For the named disturbance `−W(1−exp(−20t))`, also append the global exponential state s, with s'=-20s and s(0)=1. This permits exact rational Taylor propagation with an explicit infinite-tail bound.

Our propagator encloses initial center c with common infinity-radius rho. For M=dA, a=||M||infinity, B=||c||infinity+rho, and degree N with a/(N+2)<1, the omitted tail is bounded by `B a^(N+1)/(N+1)! /(1−a/(N+2))`. It evaluates the finite vector series exactly as Fractions. The new radius is the old radius times the scalar finite-series majorant, plus that infinite-tail bound. Final displayed endpoints round outwards on a10^-18 grid. This is ordinary validated mathematics, not a Lean certificate.

Exact counterexample with the ORIGINAL acceleration-only controller kappa0: root's numerical schedule search suggested r12 for the first0.04s, r8 for the next0.04s, then r10 for the remaining hold. Keep the original exponential disturbance W=1/2000, original reference, and zero initial error. inventor_zero_ff.py independently encloses

`0.000313158008158206 ≤ x(0.474)−q(0.474) ≤ 0.000313158008158207` meters.

The lower endpoint exceeds0.0002m. The last Taylor segment uses degree264, with the tail included; it is not an unchecked numerical peak estimate. The script binds the original profile, coefficient, horizon, and W to four matching saved comparison rows, and hashes comparison.py/results. This rate schedule was not one of those four.

Therefore a tighter finite-horizon method cannot certify a0.2mm tube for this entire original varying-rate family under kappa0. This does not mean every finite-horizon tube fails, that no tighter bound exists, or that fixed-rate cases fail. The former cube remains a sufficient but loose certificate at its much larger radius. A useful finite-horizon success must state exactly which uncertainty family it covers.

Preserves: actual-reference error dynamics, controller coefficient, initial state, reference joins, original disturbance, and admitted rate range. Breaks: fitting only endpoint rates as fixed constants; treating a sampled maximum as a continuous bound; dropping tail error; resetting physical state; or changing sigma (which changes the physical rate family).

## Transfer 2 — unexpected: rate variation demodulates a moment-canceling jerk signal

The four-pulse jerk pattern has exact moments `integral j=0`, `integral t j=0`, and `integral t² j=1/3125`. Such cancellation resembles a moment-null filter: it can suppress slow responses when the forcing is processed by one fixed convolution kernel. A varying actuator rate changes both the residual forcing and the state-transition kernel, so that cancellation need not survive.

For midpoint kappa5/48, residual acceleration-error forcing is `(r*kappa−1)j`. Choose r12 on positive-jerk phases and r8 on negative-jerk phases. Every phase's residual is positive:5/2 or5/3. Its integral over the original0.08s motion is1/6, whereas at any fixed r the integral is zero. This is an explicit admitted schedule, not a claim of worst-case optimality.

inventor_cancellation.py exact-encloses that schedule with w0 (admitted by the original W bound) and r10 after the move:

`0.000245850550989830 ≤ x(0.1)−q(0.1) ≤ 0.000245850550989831` meters.

For fixed r10 with the SAME midpoint coefficient, reference, w0, and witness time, the enclosure is approximately2.36152217e−6m, well inside0.2mm at that time. The contrast isolates a rate-scheduling effect; the fixed-rate point is not a full-horizon certificate. The separate zeroFF counterexample shows that removing the explicit r*kappa modulation does not restore arbitrary-rate safety: r still changes the transition matrix and disturbance channel.

Preserved invariant: exact signed history and the correct common kernel when rate is fixed. Falsifier: replacing the time-varying product r(t)j(t) by a product involving an average r, or transferring moment cancellation from one LTI convolution to an arbitrary time-varying plant. Next useful positive route: output-specific adjoint/support-function bounds that retain the signed forcing, then a separate robust control argument if rate variation is permitted. No such arbitrary-rate upper bound was proved here.

Requested variation-bound supplement: inventor_variation.py concatenates one original short forward move and one reverse move, with kappa5/48, fixed r8, w0, continuous q/q'/q'' joins, and retained actual/error state. This is explicitly a CHANGED-TASK negative control, not the original single-move experiment. Net displacement at0.16s is0, but exact total variation is1/3125m=0.32mm. Its error enclosure is `[0.000013266840323065,0.000013266840323066]`m, strictly nonzero. The script checks the sign of reference velocity over every quadratic phase using endpoints and any interior critical point. Therefore a bound using absolute net displacement in place of total variation would falsely predict zero error. Using the original move distance as total variation requires its monotonicity hypothesis; it cannot be carried unchanged into a reversing history.

## Transfer 3 — translation validation of the proof state and its clocks

Treat an enclosure artifact as a small executable proof whose state variables and reset maps must match the modeled trajectory. Local polynomial monomials may restart at a phase boundary because their coordinate chart restarts. The physical error state and the global exponential disturbance coordinate may not restart if the named input remains `−W(1−exp(−20t))`.

Concrete negative mutation: keep all physical/error states but reset s to1 at each phase join. This produces another bounded disturbance, but not the original named one. Exact enclosure at0.474s changes to

`0.000317087159810639 ≤ x−q ≤ 0.000317087159810640` meters,

strictly disjoint from the original enclosure. A numerical/interval program can be internally correct while proving a changed input. This mutation is not itself a counterexample to a statement quantified over all |w|≤W: both inputs satisfy that broader magnitude bound. It is a falsifier for a claimed replay of the specific saved disturbance.

Preserves: state meanings, time origin, and source-to-error-ODE relation. Breaks: treating every appended coordinate as a local monomial; importing a simulator endpoint without an enclosure; relabeling a changed disturbance as the original; or changing uncertainty quantifiers between prose and certificate. A future checker should bind the initial set, actual controller, full rate/disturbance schedule or uncertainty class, reference coefficients, reset maps, phase durations, and outward-rounding rules before accepting a bound.

## Exact model used and evidence scope

For sigma1, the three tracking errors satisfy

`e_x'=e_v`, `e_v'=e_a`,
`e_a'=−8r e_x−6r e_v−(3r/2)e_a+(r*kappa−1)j+r w`.

The derived x=q+e_x, v=q'+e_v, a=q''+e_a obey the original plant/controller on every open phase. Piecewise constant admitted rates and finite joins give a well-defined linear evolution with continuous retained states. The witness lies inside the original4.08s horizon, which can be completed with r10. It does not claim differentiability of acceleration or jerk at switches, a global peak, a full-time enclosure, controller optimality, or physical robot behavior.

Scripts: inventor_cancellation.py/json/log and inventor_zero_ff.py/json/log. Exact rational arithmetic includes every Taylor remainder; no numerical simulator state initializes the enclosure. A small SciPy calculation was used only to select the midpoint witness time, and root's separate numerical scan selected the zeroFF candidate. The decisive bounds are recomputed from zero with Fractions. Scoped Ruff lint/format checks pass. Critic independent validation requested; PM records its outcome. No original Lean result is changed.

Recommendation: NO-GO for a universal0.2mm certificate over the original entire varying-rate family with these existing controllers; the shown counterexamples already obstruct kappa0 and5/48. Root/domain handle the nominal coefficient separately. GO for a certificate format that explicitly distinguishes fixed rates, named rate schedules, and the full uncertain family, and for valid finite-horizon upper bounds on a narrower declared case. Any new rate-slew restriction, changed gains, or reference retiming is a new problem and must be labeled.

Quality: faithfulness4, reproducibility4, discrimination4, critique4, actionability3 =19/20 (95%). Subjective confidence high in the exact counterexamples; not a claim about worst-case optimality, novelty, or physical applicability.
