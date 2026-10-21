# C02 — choose feedforward for the actual performance objective

AI-written research. **GO for an enclosed affine-response optimizer and adversarial scenario exchange.** No universal optimal coefficient was established. Timed review completion is determined by `state.json`, not this draft card.

## Question, provenance and unchanged model

Which jerk-feedforward coefficient minimizes finite-horizon position error rather than invariant-cube residual or initial jerk error? The frozen source is the tracking-replans README under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/`; its hash still matches selection. Roles inspected the actual comparison and Lean artifacts. Original sources were preserved.

The plant and controller are

    x'=v, v'=a, a'=r(t)(u+w-a),    8σ≤r≤12σ,
    u=q''−8σ²e_x−6σe_v−e_a/2+κj,    e=x−q.

κ has units seconds; σκ is dimensionless. The source benchmark uses zero initial error, four constant-jerk segments [+J,−J,−J,+J], continuous q/q'/q'', followed by four seconds of hold. Its objective is peak |e_x| over motion AND hold. The source disturbance is a particular smooth bounded negative waveform; its four rates are three constants and one smooth stress signal. These are finite scenarios, not all admitted uncertainty. No slow filter or feedforward relocation from C01 was introduced.

The exact error equation is

    e'''+1.5r e''+6rσ e'+8rσ² e=(rκ−1)j+rw.

For each fixed exogenous rate/disturbance and coefficient-independent initial state, eκ(t)=b(t)+κa(t). Two basis trajectories therefore evaluate all coefficients. With known constant r, zero disturbance and zero initial error, eκ=(rκ−1)f_r, so κ=1/r gives exact zero error under the stated ODE. Ranking fixed coefficients cannot reverse with horizon in that special case. The historical reversal depends on uncertainty/disturbance, not merely a short move.

## Transfers and discriminating tests

**Chebyshev fitting and convex dual certificates.** The peak objective is a supremum of affine signed-error functions in κ. A fixed uncertainty set preserves convexity even if its maximizing waveform changes with κ. Two opposing signed sensitivities can certify a scalar minimax lower bound. Active errors need not have opposite signs: both active errors in the tested four-scenario optimum are negative. Saturation, unbound initial states and a single state-dependent-rate policy need new arguments.

**Signed-kernel and experiment-design transfer.** Horizon and rate change the weights on coefficient residuals. Exact rational Taylor/Bernstein enclosures for a declared quintic rest-to-rest probe show a two-rate ranking reversal. This probe is explicitly different from the source reference and certified only over its motion interval. Its L2 calculation is a separate objective; its motion-peak calculation addresses a peak norm but does not certify the extra four-second hold.

**Unexpected lock-in/mixing transfer.** The original jerk schedule has zero zeroth and first moments. Multiplying it by the rate schedule (8σ,12σ,12σ,8σ) gives ∫rj dt=−8σJh. Thus a positive κ can create nonzero signed forcing even when ∫j dt=0. This is an exact forcing-channel identity, not final acceleration or peak-error proof; feedback remains essential.

**Adversarial games and validation.** Tune on a small rate set, then search for a violated rate/time constraint and enlarge the set. Held-out phases immediately falsify a claim of general robustness. Pointwise interval/Hamiltonian corner algebra suggests a future adversary-search ingredient, but it is not a complete switching trajectory or global optimal-control certificate.

## Outcomes and independent checks

For the original short benchmark J=10, h=.02, σ=1, W=.0005 and full 4.08-second horizon:

| Finite scenario experiment | κ (seconds) | Peak error (mm) |
|---|---:|---:|
| Original four rates, tuned | .00280548339 | .10992335 |
| Same four, zero jerk feedforward | 0 | approximately .11245 |
| Tuned four-rate coefficient on held-out phases | .00280548339 | .30169936 |
| Enlarged seven-rate game, retuned | .01216665784 | .27414833 |

These are numerical results. Separate standard-library RK4, DOP853 dense-output/extremum refinement, and independent physical-state RK45 agree. The dense result slightly exceeds the sampled RK4 peak, as expected. Root localization is not a proof that every extremum was found. The finite-game optimum is not the robust optimum over all allowed rates/disturbances. The approximately 2.5 μm training improvement over zero feedforward is much smaller than the held-out failure.

Independent physical replay agrees with sampled inventor peaks within 4.20e−12 m. Shared nonzero-initial-condition affine superposition agrees to 6.1e−18 m. Negative controls expose resetting at reference switches (~.1215 mm difference), command clipping (~.0353 mm superposition failure), and mixing κ with σκ at σ=10 (~.1648 mm difference). These are numerical falsifiers, not hardware results.

For the declared quintic probe, two constant rates {8,12}, σ=1, no disturbance, and normalized displacement, exact motion-peak enclosures give:

| Motion horizon | Nominal κ=.1 peak | Cube κ=5/48 peak | Minimax κ enclosure |
|---|---|---|---|
| .08 s | [0.13730314,0.13733595] | [0.14876733,0.14877061] | [0.1014475176,0.1014501895] |
| .25 s | [0.07584756,0.07587098] | [0.07155520,0.07158486] | [0.1028716770,0.1028791785] |

The exact Fraction results retain more digits than these outward summaries. Critic independently reconstructs the Taylor kernel, remainder and Bernstein bounds using a different conversion. A numerical hold probe finds no larger peak, but the available invariant-cube bound is too loose to certify that; full-hold equivalence stays open. Initial failed ranking prediction is preserved.

Root's separate constant-jerk/two-rate numerical probe shows that peak and endpoint objectives differ even at long horizons: r=12 has a small step-response overshoot. Its limiting peak-tuned coefficient is about .10415785, rather than silently substituting the endpoint steady-state value 5/48. This probe supplies an objective-mismatch control, not an original-benchmark solution.

## Proof and acceptance boundaries

Ten distinct isolated Lean declarations cover scalar L2 completion/optimality, reciprocal-rate residual cancellation, conditional affine-tube convexity, two-active lower bounds, pointwise rate/disturbance corners, basis approximation error and objective regret. Root and critic replayed promoted files with standard permitted axioms. They do not formalize ODE existence/uniqueness, exact benchmark trajectories, extremum completeness, arbitrary-rate optimality or physical calibration. Exact Taylor/Bernstein certificates are independently checked Python arithmetic, not kernel-certified integration.

If basis errors satisfy |b−b̃|≤ε_b and |a−ã|≤ε_a, the response error is at most ε_b+|κ|ε_a. Uniform objective error ε plus surrogate optimization gap η gives true regret ≤2ε+η. The new Lean lemmas check this conditional budget; present numerical solver agreement does not establish its hypotheses. Convex uncertain approximation is established literature, not a novelty claim (`pm_sources.md`).

## PM decision and next action

**GO**, after all 60 initial reviews, for one 30-minute block on full-horizon basis enclosures and a checked finite-game optimizer. Keep the original four-segment reference, 4.08-second horizon, σ=1 and fixed four-rate/disturbance set. Target objective error at most 1 μm per compared coefficient, enough to resolve a roughly 2.5 μm gain if optimizer error is also budgeted. Cover every time, switch and hold interval. Declare a coefficient interval and either certify exclusion outside it or state the bounded scope. Preserve all numerical/physical-coordinate negative controls.

Then use declared held-out phases as falsification cases; broader scenario search is an experiment, not proof of complete uncertainty coverage. Require a certified improvement, a tighter failure bound, or a materially different informative test before renewal. **HOLD** continuous all-rate/all-disturbance optimality, full physical validation, novelty, and the quintic probe's hold extension. The original tracking theorem is not refuted by a finite-scenario tuning failure.

Quality: faithfulness 4/4, reproducibility 4/4, discrimination 4/4, critique 4/4, actionability 3/4 = **95/100**. Subjective confidence is high in the conditional algebra and scoped comparisons; universal robust performance is unresolved, with no calibrated probability assigned. Root PM and the three reused roles used the inherited working model, exact runtime ID unavailable. No model-family diversity, Spark inference, package installation or hardware use is claimed.
