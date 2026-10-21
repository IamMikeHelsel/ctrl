# C02 cross-discipline inventor

AI-written research; inherited root model, exact runtime model identifier unavailable. Root owns timing and the PM decision. This role wrote only `cards/C02/inventor*`. No original controller, task, approved challenge, hardware, or remote resource was changed.

## Frozen objective and source

Choose the scalar jerk-feedforward coefficient c for finite-horizon peak position error in the fixed architecture

    u = q'' − 8σ² e_x − 6σ e_v − e_a/2 + c j,
    a' = r(t)(u+w−a).

This is distinct from minimizing an invariant-cube residual, initial jerk error, command variation, or settling error alone. Inspected the local source snapshot and `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/tracking-replans/comparison.py`. The numerical probe retains its short-high-jerk reference: J=10, four stages of h=.02 seconds with signs +−−+, then a four-second hold. Total horizon is **4.08 seconds**, σ=1, W=.0005, w(t)=−W(1−exp(−20t)), and all initial tracking errors are zero. The source's four rate signals are 8,10,12 and its declared smooth phase-aligned stress signal. Those four signals are a finite sample of the admitted rate band, not a worst-case characterization.

## Transfers, preservation and failure boundaries

**1. Chebyshev approximation with signed sensitivities.** For any fixed rate, reference, disturbance and common initial condition, write d=σc. Linearity gives

    e_x(d,t) = b(t)+d z(t).

Here b solves the original error ODE at c=0. The sensitivity z starts at zero and satisfies the same homogeneous error dynamics with input rj/σ. Thus the original peak-position objective over a declared scenario set becomes a convex supremum of absolute affine functions of d. Two active signed lines with opposite slopes can provide a scalar minimax lower certificate: mix them with nonnegative weights summing to one and zero weighted slope. Their weighted intercept is a coefficient-independent lower bound; if every line lies below it at the proposed coefficient, the finite problem is solved. This preserves the exact controller and position objective and needs no coefficient grid scan.

The falsifier is a nonzero affine superposition residual, an unmatched initial state/disturbance, or an omitted larger-time/scenario maximum. Saturation, c-dependent disturbances/rate schedules, state-dependent plant nonlinearities, or changing c online can break this affine reduction. An interval maximum between time samples can invalidate a sampled minimax claim.

A subtle boundary matters: **opposite active error signs are not required**. In this example both active errors are negative; their sensitivities have opposite signs. Blindly importing ordinary alternating-error-sign pictures would reject the correct subgradient condition. The exact toy errors −1+c and −1−2c have global minimax c=0, both active errors −1, and signed-slope dual weights 2/3 and 1/3. This toy is a counterexample to an overstrong analogy, not a new plant model.

**2. Signed impulse kernels and experiment design.** With fixed r and zero initial error, the transfer denominator is

    s³ + (3r/2)s² + 6rσ s + 8rσ²,

and the forcing is (rc−1)j+rw. Unlike an absolute residual bound, the finite position response retains the signs, timing and filtering of this forcing. At w=0, c=1/r cancels the forcing exactly for every horizon; coefficient ranking cannot be assumed to reverse merely by changing the horizon in that fixed-rate case. With varying r, the time-varying state transition kernel must be retained rather than replacing it with a single time-invariant impulse response. The experiment-design transfer is to pick rates and observation times that reveal opposing coefficient sensitivities. Falsifiers include confusing a low forcing integral with low position error, or calling the sampled maximizing rate an actual adversary over all admitted rates.

**3. Unexpected transfer: lock-in detection and frequency mixing.** The four planned jerk stages have zero zeroth and first signed moments. Phase-aligned rate modulation can turn this otherwise cancelling jerk into a nonzero low-frequency forcing component. For the explicitly declared piecewise-rate probe (8σ,12σ,12σ,8σ),

    ∫j dt=0,    ∫t j dt=0,
    ∫rj dt=−8σJh,    ∫t rj dt=−16σJh².

Therefore positive c injects raw forcing impulse c∫rj even though ∫j=0. At the numerical parameters and c=.1, that impulse is −4/25; at c=0 it is zero. `inventor_moments.py` verifies these identities exactly with rational arithmetic. This preserves the reference and controller but uses a declared alternative bounded rate schedule and w=0 for the forcing-channel diagnostic. It does **not** identify the forcing integral with final acceleration error: the feedback terms still contribute to e'''. Neither zero impulse nor a small impulse proves a small peak position error. The phase-shift tests below provide a falsifier for any claim that this one diagnostic predicts every trace.

**4. A finite adversarial game.** The two active time/scenario constraints can be viewed as a mixed adversary certifying a lower bound, while fresh phase-shifted rate scenarios challenge the selected coefficient. These weights are dual mathematical weights, not a physical random switching law. Adding a scenario changes the finite approximation to the original robust objective, not the motion task or controller. A finite-scenario optimum can lower-bound the ideal all-rate minimax value when computed exactly, but supplies no all-rate upper guarantee. Our computed values remain numerical approximations to those finite quantities.

## Tests and results

`inventor_minimax.py` independently integrates six basis states with pure-Python RK4 on step sizes .001 and .0005 seconds, matching every jerk switch. All coefficients use the same traces through the affine response. The fine sampled optimum is c=.002805273970 seconds, sampled peak .109919983928 mm. Baselines over the same four source scenarios are:

| coefficient | largest sampled position error |
|---|---:|
| c=0 | .112442667111 mm |
| c=.1 nominal | 1.883686835868 mm |
| c=5/48 cube | 1.960181994495 mm |
| tuned c | .109919983928 mm |

The two active sampled constraints are fixed r=8 at t=.0625 and phase-aligned stress at t=.734. Their signed slopes are approximately −.000899264 and +.016055025; dual weight .946959471 gives a numerical sampled dual gap about 1.4e−20 m. This is not a rational or interval certificate. Halving the step changes c by approximately 2.49e−7 seconds; tiny peak improvements should not be overstated.

`inventor_dense.py` uses a separate DOP853 implementation with dense output and searches sign changes of error velocity to refine peak times. It finds c=.002805483390 seconds and peak .109923350260 mm. Active times are .062701406561 and .733800724871 seconds. Both errors are negative. The source stress maximum occurs well after the .08-second motion ends, so discarding the four-second hold would silently change the objective. The finite-grid result slightly underestimated the continuous-time peaks, as expected. Dense derivative-root searches remain numerical: root completeness and interpolation error are not interval-certified.

Three held-out smooth rate signals use phases π/2, π and 3π/2 in the same bounded source rate formula. They preserve the reference, horizon, disturbance and initial state. The four-rate tuned coefficient reaches **.301699364143 mm** on these held-outs, much larger than its training peak. Enlarging the finite game to all seven rates gives c=.012166657841 seconds and peak **.274148329939 mm**. This is a concrete scenario-overfit failure and a discriminating next direction, not an all-rate solution or a universal coefficient recommendation.

The initial NumPy/SciPy environment checks failed without modifying environments. The PM supplied an existing compatible interpreter; DOP853 ran using `uv run --no-project --python /usr/local/bin/python3 python ...`. No packages were installed. All three own Python files pass Ruff. Exact rational moments, numerical integrations and sampled dual calculations have separate evidence levels; none is reported as a Lean proof or physical validation.

## Proposed gate

**GO** for an exchange algorithm that alternates convex scalar coefficient fitting with a bounded, declared rate-scenario challenge, retaining the original full horizon. The next informative test is to freeze the seven-scenario coefficient, seek one additional admissible phase/frequency schedule that increases its peak, and independently enclose the active time extrema and two-line dual bound. Improvements must be measured against the same reference, initial state and uncertainty set. A rigorous all-rate result would additionally require an upper-bound argument over that uncertainty set.

**NO-GO** for calling either cube-residual optimum or nominal initial-jerk optimum a universal finite-horizon winner; for requiring opposite error signs as the minimax certificate; or for presenting a sampled fit as a robust guarantee. **HOLD** certified continuous-time/global-rate optimum pending interval extremum bounds and an adversary-completeness or robust upper-bound bridge. No architectural relocation of feedforward was used.

Quality: faithfulness 4/4, reproducibility 4/4, discriminatory value 4/4, critique 4/4, actionability 3/4 = 19/20 (95%). Subjective confidence is high in the affine derivation and finite-scenario failure mechanism, moderate in the quoted numerical last digits, and uncalibrated for a certified all-rate optimum.
