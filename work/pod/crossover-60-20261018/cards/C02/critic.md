# C02 independent critique

AI-written by the independent critic, inherited root model; exact model ID unavailable. No original files or approved challenges edited. Numerical integrations, exact arithmetic, standalone Lean lemmas and physical validation are separate evidence levels.

## Source binding

Read the frozen source snapshot, original comparison.py and TrackingReplan.lean. The comparison objective is sampled peak absolute position error over four jerk stages plus a four-second hold, T=4h+4. Endpoint error is separately reported; L2 is not that objective. Original references use jerk [+J,−J,−J,+J], with continuous position/velocity/acceleration and state carried across each switch. No derivative is required at the switch itself by the original segment theorem. Initial actual and reference states are zero. The declared negative disturbance is −W(1−exp(−20t)), not every bounded disturbance. The hand-selected smooth rate is not a worst-case search. Sigma changes both feedback gains and the assumed actuator-rate band. There is no saturation or delay in the frozen model.

The physical coefficient κ has units seconds; d=σκ is dimensionless. In SI units the disturbance is acceleration. Never compare coefficient-dependent invariant cubes as though they were the same initial-condition uncertainty set or task tolerance.

## Exact reasoning

For fixed exogenous r(t), w(t), reference j(t), and coefficient-independent initial errors, the original architecture gives

    e''' = −8rσ²e −6rσe' −1.5re'' +(rκ−1)j +rw.

Linearity and uniqueness give eκ=e0+κh, where h has zero initial state and forcing rj. This is an analytical deduction, not a newly kernel-checked ODE theorem. At a known constant rate with w=0 and zero initial errors, κ=1/r cancels tracking error exactly. At short times with j(0)=J and w(0)=0, e(t)=(rκ−1)Jt³/6+o(t³). Hence the initial-jerk objective and reciprocal-residual objective legitimately differ; the source already says this.

Suprema of |e0+κh| over a coefficient-independent set of scenarios and times are convex. A finite sample/scenario optimum is a lower bound on the unknown full supremum minimax value. It is not a guaranteed upper bound or proof of robustness. State-dependent rates, coefficient-dependent uncertainty sets, and saturated commands require a new argument.

## Independent executable checks

critic_physical.py uses RK45 on the actual (x,v,a) plant, with independently constructed continuous reference segments. It does not import the producer's basis functions. All seven declared rate waveforms at the inventor's sampled-fit κ agree with the producer's sampled peaks within 4.20e−12 m. The original-four sampled peak is about 0.109920 mm; phase-shift heldout rate phase3 produces 0.301700 mm. All rates remain in the original allowed band. Numerical refinement is not an interval enclosure.

Affine superposition at every sample with a shared nonzero initial state agrees to 6.1e−18 m. Negative controls are consequential: resetting state at switches changes the trajectory by 0.1215 mm; command clipping breaks affine superposition by 0.0353 mm; treating d as κ at sigma10 changes response by 0.1648 mm. These are deliberately changed implementations/models, not allegations of source bugs.

The inventor's two active signed lines have opposite slopes, a convex dual weight in [0,1], zero weighted slope to floating precision and matching primal/dual sampled values. This verifies algebra on floating surrogate data, not exact continuous plant data. Dense-output extrema localization remains numerical, and sign-change bracketing alone does not certify finding every stationary point.

critic_kernel.py independently reconstructs the domain's polynomial kernel using the scalar third-order recurrence rather than its matrix recurrence. All four rational L2 interval endpoints and both coefficient enclosures match exactly. The analytic remainder follows from the matrix infinity norm, |Q'''|≤60, exp(K)≤3^ceil(K), and integrating the Taylor-tail bound. The squared-integral error bound ε(2Σ|coeff|+ε) is valid. This is a useful declared extension using a quintic reference, two constant rates, zero disturbance and L2 over the move. It changes the original peak/reference problem and is not its solution. Its rational arithmetic is independently checked; the full remainder argument is hand-derived, not kernel-proved.

## Gate recommendation

GO for a bounded exchange experiment using the original reference, fixed objective, a declared rate/disturbance class and independent error enclosures. Keep the original general question open. The next experiment should search for a new admissible rate waveform violating the current candidate, add it to the finite game, and preserve a separate numerical lower bound and certified upper bound. Rate and disturbance limits must be fixed before claiming robust optimality. If arbitrary measurable rates are intended, finite phase shifts alone cannot close that claim.

No universal optimum, original-source bug, novelty or physical robot result is established. Subjective confidence in the conditional affine/convex reduction is high; this is not a calibrated success probability. Rubric quality: 18/20 (source binding4, independent checks4, negative controls4, claim calibration4, closure2); continuous-time/all-uncertainty certification remains open.

## Final certificate audit and objective extension

Both pm_convex.lean theorems independently compile with only propext, Classical.choice and Quot.sound. They prove a generic two-line lower bound and a convex affine tube, not plant response binding or any numeric optimal coefficient. Opposite signed slopes suffice even when both active errors are negative. critic_dual_negative.json gives an exact integer failure after dropping the nonnegative-weight premise. A κ-adaptive maximizing adversary does not destroy convexity when it selects from the same fixed waveform set; coefficient-dependent admissible sets are the actual concern.

The first independently compiled domain_affine.lean draft failed (missing tactic import and unfinished simplification), with sorryAx in diagnostics. That failed log is preserved in critic_domain_affine_failed.log. The corrected frozen file independently compiles all three scalar identities/inequalities with permitted axioms; critic_domain_affine.log contains the successful audit. These are conditional quadratic and residual algebra, not an ODE theorem or Taylor-remainder proof.

The final domain extension also encloses the two-rate quintic motion-only peak. critic_kernel.py independently computes all 65 dyadic sample values by Horner evaluation and every local Bernstein control coefficient by direct Taylor translation/power conversion, instead of the producer's de Casteljau subdivision. All four exact peak lower/upper endpoints match. Thus the declared motion-only peak ranking reversal is independently supported by exact arithmetic plus the hand-derived remainder. The original four-second hold and original jerk reference are still outside this certificate. No extrapolation to their peak is accepted.

Scoped Ruff initially flagged late-bound loop variables in critic_physical.py; explicit default bindings fixed the issue, preserving the already synchronous integration semantics. Final scoped Ruff and format checks pass. No repository-wide or physical-device checks are implied.

The two final pm_corner.lean lemmas and three pm_enclosure.lean lemmas independently compile with permitted axioms; logs are critic_pm_corner.log and critic_pm_enclosure.log. The first pair is pointwise scalar Hamiltonian algebra only. It neither constructs an admissible maximizing trajectory nor proves global worst-case or absence of chattering. The latter three transfer already-established basis error bounds and objective approximation errors; it does not establish such bounds for the computed trajectories.

The proposed next gate of at most 1 μm objective enclosure error per candidate is meaningful for a roughly 2.5 μm predicted improvement: independent adverse errors leave roughly 0.5 μm strict separation. The entire 4.08-second objective, all four declared scenarios and switch boundaries must be enclosed. Uniform coefficient optimization requires a declared bounded κ interval (ea+sup|κ|eb≤1 μm) or certified exclusion of coefficients outside it. The 2ε regret theorem assumes an exact surrogate comparison; a numerical optimization gap η adds to the bound, giving 2ε+η. The heldout phases should then challenge the newly certified finite game, not be relabeled an arbitrary-waveform certificate. No further investigation block was started.

Final updated pm_enclosure.lean independently recompiled successfully after adding approximate_objective_regret, now explicitly proving 2ε+η. All three declarations use only propext, Classical.choice and Quot.sound. Audited SHA-256: abdcdb2df9ac4caf07a8d63e88ec4e6dc443676dbe2bd144c43ad862a039f74a.
