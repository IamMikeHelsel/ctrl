# C11 domain — exact initial facets versus delayed entry

AI-written; inherited root model, exact identifier unavailable. Original files remain unchanged. This review concerns the source scalar reference model, not a robot or new hardware result.

## Frozen source recovery

The milestone01 report explicitly deferred family149 active-facet entry. The actual `active_facet_screen.py` is a weighted-cube shrink calculation: weights(1.02,1.01,1), targetweightedradius.045 and a separately supplied residual bound. It is not an initial sensor-box admission theorem. Its corner checks and candidate capture time do not establish trajectory existence, a sampled detector, or a pending-to-hold handoff.

AdaptiveAdmission03 uses the full physical state(x,v,a), transform

    z=(x−c, x−c+v/4, x−c+v/2+a/16), R=2221/40000=.055525.

It chooses c=m_x+m_v/4+m_a/32 once from the initial reading, with the original rectangular guard |m_v|≤.02,|m_a|≤1.25. Sensor errors are(.001m,.01m/s,.05m/s²). Pending command−1.21 persists through startupD≤.0005s; targeterror≤.01 lies outside clipping. Rate can vary in[8,12], total reading age≤.001s, and the original stampzero is retained. Position is unrestricted by this guard. Source pending dynamics are x′=v,v′=a,a′=r(−1.21+d−a). The later clipped holding law is−8(x−c)−6v−a/2, and its original proof derives the complete-history residual. A new initial test cannot simply assume that later residual or delete pending time.

## First transfer: polytope support functions

For universal containment in a polytope, each facet support must satisfy its bound. The extrema of different facets need not occur at one shared state. Therefore an unattainable combination of coordinatewise worst cases cannot improve an already exact facet-support test. This corrects the proposed obstacle in the frozen roster; it does not invalidate directional dynamics as a separate opportunity.

At timestampzero, writing the true state as m+e gives

    z0=e_x−m_v/4−m_a/32,
    z1=e_x+e_v/4−m_a/32,
    z2=e_x+e_v/2+e_a/16+m_v/4+m_a/32.

The exact uncertainty supports are(.001,.0035,.009125). Each bound is attained by a permitted sensor corner. Consequently robust containment of the entire sensor box in the unchanged cube, with the unchanged center, is exactly

    |8m_v+m_a|≤928/625=1.4848,
    |m_a|≤2081/1250=1.6648.

The z0 condition is redundant because its nominal magnitude equals z2's while its error support is smaller. No probability, independence distribution, or simultaneous attainment of all absolute maxima is required. The uncertainty is the source deterministic Cartesian box.

`domain_entry.lean` proves the actual coordinate substitution, this necessary-and-sufficient quantified real guard, inclusion of the old rectangular guard, a strict-widening witness(.3,−1), and rejection of the source's attempted wider rectangular corner(.03,1.25). All five declarations compile with permitted axioms. The proof needs only two sensor corners for necessity and bounded linear inequalities for sufficiency.

`domain_vertices.py/json` independently enumerates all8sensor vertices for5readings. The old corner(.02,1.25) passes. The widened corner(.03,1.25) reaches.0556875>R and fails. The new(.3,−1) reading passes only the initial test. The inventor's new-band upper corner(.03,1.24) reaches.055375<R. These are exact Fraction calculations, not delayed-admission results.

## Second transfer: directional active facets and a failed promotion

The exact initial guard cannot replace the full delayed guard wholesale. For example choose m_v=−.2,m_a=72/625 and all three negative sensor errors. The attained lower z2 facet is exactly−R, with truev=−.21,truea=.0652. Legal pending parameters r=8,d=0 give

    z2′=v+a/2+8(−1.21−a)/16=v−.605=−.815.

Thus a differentiable pending trajectory leaves the cube immediately. This refutes promotion of initial containment to universal delayed admission; it does not refute the original C3 theorem, whose guard rejects this reading. Critic supplies a separate exact closed-flow witness.

The obstruction extends across the entire attained lower strip facet. If8m_v+m_a=−928/625 and|m_a|≤2081/1250, the negative sensor corner lies on z2=−R and its legalr8,d0 pending derivative is≤−237/400=−.5925. Conversely, the corresponding attained upper facet has pending derivative≤−463/5000=−.0926 for every admittedrate/disturbance. `domain_lowerface.lean` checks these three exact source-coefficient claims. These algebraic inequalities alone are not a full trajectory/existence theorem.

## Positive route and independent check

Inventor's positive band m_v∈[.029,.03],m_a∈[1.23,1.24] retains the same center, pending command, sensors and delay. The idea is to show z0,z1 stay negative and increase, while z2 stays positive and decreases during startup. This permits an initialz2 margin too small for the old symmetric coordinate-drift envelope. I independently checked the proposed bounds: a∈[1.16488,1.3],v∈[.01835,.04065] give z0′>0,z1′>0 and z2′≤−.55935 using the shared acceleration term (the inventor's weaker−.49179 bound is also valid). The later feedback-slope≤8 budget still requires its source-bound proof. Inventor owns that certificate and root owns any full delayed-hold wrapper.

This is where active-facet geometry can reduce conservatism: preserve the direction and shared variables of the pending flow, rather than dropping a necessary facet because its maximizer differs from another facet's maximizer. A center redesign is a separate controller-policy change and must be labeled; this domain test keeps the original center.

GO for a source-bound direction-aware startup interface connecting the new band to the unchanged later age/clipping proof. NO-GO for improving exact initial containment merely by removing unattainable joint box corners, or treating the exact widened initial strips as delayed admission. HOLD a full theorem for arbitrary readings until the pending prefix, later residual and existence conditions are bound together. Quality18/20(90%); subjective confidence high for exact static geometry and signed facet algebra, with full delayed integration owned by the remaining pod work.

## Actual pending-execution bridge

`domain_actual_startup.lean` imports the actual source `AdaptiveAdmission.Execution` and proves its continuous pending acceleration barrier from the explicit initial condition `|f 0 2|≤13/10`. This removes the old rectangular measurement guard from that one lemma, without changing the execution, command, clock, rate, physical target-error, or one-sided derivative fields. Its proof is the source startup barrier proof with the old `initial_bounds` invocation replaced by the explicit initial premise. The new positive band's measured acceleration≤1.24 plus unchanged±.05 sensor error implies |a0|≤1.29<1.3. This is a source-bound ODE bridge, not just a restated face inequality. Compilation and independent replay status are recorded separately; a printed statement alone is not acceptance.

The companion replay script fresh-compiles only this new module using the original pinned4.35 runtime. It checks the accompanying cached `DigitalHold` and `AdaptiveAdmission` source hashes against originals, and records their olean hashes; it does not claim a fresh rebuild of the complete original proof closure. The inventor's separate generalized holding adapter uses explicit startup-cube and startup-slope premises. Combining these pieces into an all-time theorem for the new measurement band still needs the intervening velocity/acceleration envelopes and directional coordinate arguments; no original `Admitted` guard is fabricated.

I independently compiled critic_pending's four declarations with exit0 and permitted axioms. Its exact scalar-flow expansion and strict-escape result verify the lower-face negative control. The interpretation E=exp(−8t) as a concrete source trajectory is a mathematical binding argument, not an imported actual-Execution existence theorem.

Actual startup producer result: exit0, one declaration with only propext/Classical.choice/Quot.sound, frozen SHA256 `8d503522f67976c17521e77e9522fd28289eaec9e6bb5f30bfdb29fdf9d16265`. Independent critic replay requested; this closes the acceleration-barrier bridge only. Scoped domain Python Ruff check and formatting pass.
