# S03 domain — finite implementation error interface

AI-written; inherited root model, exact identifier unavailable. Original source and approved challenges are unchanged. This is a normalized second-order scalar controller, not the third-order lag plant used in other cards, and not an industrial machine claim.

## Source and binding

The inspected owning files are the frozen notebook `lean-controls/LeanControls/Quantized.lean`, its Sampling/RobustPD/SampledPD/PD/Discrete dependencies, README, and the source safety-filter adjacency review. Quantized's definitions are explicitly noncomputable real mathematics. No finite-word executable is proved by its `rounding_error` theorem.

The invariant is E(x,v)=5x²+2xv+v²≤1/10. Nominal feedback is u0=−2x−3v. The source quantizes the current true x and v to nearest real gridδ=1/10000, then clips the computed feedback to[−1,1]. It holds the delivered acceleration plus one constant physical disturbance w over the actual interval h∈[1/20,1/2]. The exact physical endpoint is x+=x+hv+h²(u+w)/2, v+=v+h(u+w). Source rounding contributes at most5δ/2=1/4000 to command error; physical |w|≤1/4000 makes total1/2000.

The source endpoint induction retains actual x,v. Replacing these by a rounded internal prediction is a new state-estimation premise. Likewise, asynchronous capture, stale samples, within-hold varying disturbance, dropped updates, or h outside the admitted interval need new bounds. Quantized itself proves sampled endpoint energy; it does not certify every intersample state.

## Transfer 1: refinement through a delivered-command contract

`domain_contract.lean` imports actual Quantized and proves five lemmas. Any delivered held command u satisfying

    |u−(−2x−3v)|+|w|≤1/2000

inherits the unchanged one-step invariant and the actual-state trajectory induction. The command may arise from any implementation whose error is separately checked. The composition interface makes the channels explicit:

    |xd−x|≤Ex, |vd−v|≤Ev,
    |a−(−2xd−3vd)|≤Ea,
    |u−clip(a)|≤Ed,
    2Ex+3Ev+Ea+Ed+W≤1/2000.

Here Ea includes actual arithmetic behavior; an overflowing operation does not satisfy a small Ea merely because the final result is clipped. Ed includes the delivered output's deviation from the exact real clamp, including DAC realization. The clamp's nonexpansiveness relative to the admitted nominal command is reused from the source. Sensor fidelity and arithmetic semantics remain visible assumptions, rather than a claim that the mathematical quantizer already implements them.

All five new declarations producer-compile with only propext/Classical.choice/Quot.sound. `domain_replay.json` records pinned Lean4.35 and hashes of the six unchanged local source dependencies and their reused oleans. The new module is fresh compiled; the dependency closure is hashmatched, not freshly rebuilt. Independent replay is requested from the critic.

## Transfer 2: exact support bounds for range analysis

The source uses u0²≤10E. A sharper exact identity is

    4u0²+(13x+v)²=37E.

Thus the energy sublevel implies |u0|≤sqrt(37/40). Convenient rational enclosures are |x|≤.16, |v|≤.36, |u0|≤.97. `domain_range.lean` proves that identity, those three bounds, and that a raw error≤.03 keeps the computed request within the source actuator range. These are useful inputs to finite-word range analysis; they do not by themselves prove any programming-language arithmetic semantics. Inventor and root own the concrete integer implementations and overflow negatives.

## Transfer 3: reuse unused contraction margin

The original budget1/2000 is sufficient, not sharp for the existing proof. Sampling.robust_step gives the source contraction239/240 and error coefficient1446; integrated held acceleration error is bounded in Euclidean state norm by3D/5. Therefore exactly the same proof accepts any total errorD satisfying

    1446(3D/5)²≤1/2400.

`domain_budget.lean` checks this parametric step and the rational choiceD=1/1250=.0008. This permits an additional .0003 implementation allowance beyond the original .00025 quantization plus .00025 physical disturbance, with unchanged controller, hold range, state region, and plant model. It is a sufficient certificate, not an optimal robustness radius. A rejected larger D only fails this bound; it does not by itself prove an unsafe trajectory.

This matters because the source's stated .0005 allocation has no room for appended errors, while the underlying contraction has usable slack. The implementation should consume a declared joint budget, not silently add errors to a fully allocated bound.

## Prior art and next test

Primary paper checked: [Bohrer et al., VeriPhy, PLDI2018](https://www.cs.cmu.edu/~smitsch/pdf/VeriPhy.pdf), introduction and trusted-base discussion. It already develops the real-model to machine-word interval arithmetic to verified executable route. Therefore refinement/error accounting and verified compilation are not claimed as new concepts here. Our bounded result is a source-specific reusable interface with explicit arithmetic and delivery premises.

GO for a fixed-width implementation whose every intermediate is range-certified, whose exact integer result is connected to the declared real decoding, and whose input/output error consumes this budget. HOLD end-to-end executable or hardware assurance until compiler semantics, acquisition/actuation timing, and actual physical residual are bound to the same statement. Quality18/20(90%); subjective confidence high in the algebraic interface, not a probability of implementation or physical safety.

## Independent discriminating overflow test

`domain_independent_words.py/json` independently reconstructs the inventor's declared Q16 modulo16 arithmetic, without importing producer code. At true x=−.05,v=.349, E=.099401; all four corners of the nearest-grid cell also satisfy E<.1. Correct widened arithmetic produces count−62062, while explicit modulo16 intermediates produce3474. At unchanged source h=.5,w=0, the correct output produces endpointE=15205710936853/1073741824000000<.1, but the modulo output producesE=349450198104853/1073741824000000>.1. This is an actual endpoint failure of the declared bad arithmetic on a robustly admitted cell, not merely a failure to establish its error bound. Both outputs remain inside actuator limits, so final clipping does not repair it. The distinction between explicit modulo arithmetic and C signed-overflow/integer-promotion semantics is essential; no existing source implementation bug is alleged.

`domain_overflow.lean` states the same initial point, four cell corners, and the two exact source-energy endpoint inequalities. Its arithmetic input/output binding is independently reconstructed in Python; it does not formalize a programming language or compiler. Compilation status is recorded separately. Critic_boundaries' three lemmas were independently replayed successfully: a safe rounded center can hide an unsafe true point, zero-command fallback is not a safe source fallback, and stale sensing can exceed the original sensor-rounding channel.

Final producer acceptance: all15 declarations across contract5/range3/budget3/overflow4 compile with standard axioms. The initial range proof had an ambiguous `unfold control`; the failed log is preserved and the fully qualified repair passes. Critic independently accepted contract5; other frozen modules were sent for independent replay. See domain_acceptance.json and role-specific critic manifests for final consumer status.

## Retained-history decimal/DAC composition supplement

`domain_decimal.lean` combines the actual imported source contracts with a declared decimal implementation interface. Input integer codes decode at scale10000, and the widened integer dot product decodes exactly as−2xd−3vd. This lemma concerns integer mathematics; root/critic separately check bounded intermediates, while compiler refinement remains outside it.

For a captured state(xs,vs) and current true state(x,v) connected by a retained previous constant accelerationb over ageτ,

    x=xs+τvs+τ²b/2, v=vs+τb,
    control(xs,vs)−control(x,v)=2τv+(3τ−τ²)b.

CurrentE≤.1 gives |v|≤.36. If0≤τ≤.5 and|b|≤1.00025, the stale command error is at most3.72075τ−1.00025τ². The negative quadratic term comes from preserving the shared acceleration; independent coordinate boxes would lose it. A concrete certified allocation usesτ≤1/20000, decimal halfcells±1/20000, exact widened dot, DAC deviation≤1/10000 from the real global clamp, and next held physical disturbance≤1/4000. Staleness is then≤3/16000, and total error≤.0007875<.0008. The statement also proves actual|u|≤1 using the admitted nominal-command margin. All times are normalized source units; no SI timing or measured hardware latency is inferred.

The current-energy premise is deliberate. A capture-time cell test does not initialize current-time energy after motion. An initialization adapter can propagate the complete capture cell and the independently justified old-acceleration interval through the exact known-age affine hold map, then test all eight vertices. Convexity of sourceE makes this sufficient for that box; the full vertex-checker theorem is not yet formalized here. `domain_age_gate.py/json` gives a passing origin cell and a rejected cell centered at decimal counts(−500,3499): its capture maximumE=.09998001, but its propagated outer box atτ=.00005 containsE≈.10001353. This example allows a prospective pending old command up to actuator authority; it is NOT asserted reachable under already-running correct quantized feedback, which imposes additional state/command correlation. Rejection of an overapproximating box is not proof that a particular correlated execution is unsafe.

A mathematically useful extension survives old hold boundaries. For absolutely continuous retained motion with pointwise|a(s)|≤A, stale feedback difference is2τv_current+∫₀^τ(3−2s)a(s)ds. The kernel is nonnegative forτ≤1.5, giving the same.72τ+A(3τ−τ²) bound. This integral identity and regularity/actual-history bridge are hand-derived; the new Lean theorem proves only the explicit single-hold equations. The source's next-step physical disturbance remains one held value, not arbitrary pointwise forcing. Known-age and old-history conditions must not silently replace uncertain timing or a reset estimate.

Supplement producer acceptance: decimal5 compiles exit0 with standard axioms, bringing domain total to20. One harmless unused-variable warning is retained. Its own three imported domain modules were rebuilt to oleans from their frozen accepted bytes; original source dependencies remain cached as disclosed. Independent decimal replay requested.

Precise sufficient allocation: Ed+Ea+3.72075τ−1.00025τ²≤.0003 after fixing the decimal halfcell and physical-disturbance budgets. Atτ=1/20000 the remaining DAC plus extra-arithmetic allowance is182344001/1600000000000≈.000113965000625. domain_allocation.json records exact rational cases; this is not an optimal frontier. Critic_machine4 was independently compiled successfully with standard axioms and matching source hash, establishing its stated universal integer range obligations, not C operational semantics.

Independent readmission audit: inventor_readmission5 compiled with exit0, unchanged hash74fab9e1e92df9375b5390467b90afde0cffde6157f989a5be1980e1064ab1b9 and standard axioms. I independently checked its algebra: tighter Young energy accounting gives next trueE≤29866837/300000000 forD=.0008; every fresh synchronous decimal-cell corner lies within a fullLSB of that endpoint and hasE≤29967661/300000000<.1. This supports repeated fresh-cell acceptance after a valid initialized step. It supplies neither first-state initialization nor stale sensing nor fallback safety after an assumption violation.

PM initialization statement audit: the integer four-corner threshold40000000 is scaled by400000000 and correctly entails the local quadraticE≤.1 for the same current x,v satisfying ADC halfcell premises. LocalE=5x*x+2x*v+v*v is ring-identical to actual source PD.energy, but this final definition binding is hand-checked across the separate toolchains unless a later explicit composition supplies it. The native C experiment returns integer counts; it does not itself deliver a physical DAC command.

Final independent PM replay: pm_cell2, pm_encoding4, pm_initialization1 all fresh compiled in private domain_initialization_env with exit0 and only standard axioms. Original source hashes matched copies and postcompile sources. This accepts the generic local-quadratic initialization theorem; the stated actual-source ring-identity and same-event timing caveats remain.
