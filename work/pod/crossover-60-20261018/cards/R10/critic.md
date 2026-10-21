# R10 independent critique

AI-written independent critic; inherited root model, exact identifier unavailable. Original source and approved challenges preserved. This is a fresh candidate investigation, not a modification of the frozen moving-goal-08 comparison.

## Binding to the original question

The actual source requires reference velocity ≤0.1 m/s, acceleration ≤0.5 m/s² and jerk ≤7.5 m/s³ together with authoritative admission, causal deadline service, initial physical progress ≥1 mm at 0.5 s, and physical position/speed/acceleration tolerances 0.2 mm / 0.001 m/s / 0.02 m/s² from the deadline through 2.5 s. Original remain tests are sampled. These reference limits are not limits on actual plant jerk or acceleration. The original numerical conformity allowance is 1e−10 in the respective SI units; the rational checks here need no such allowance.

The source correctly distinguishes signed-event FIR history, native executed q/v/a state, and physical x/v/a. All methods receive both proposals. Rejected FIR proposals remain physical tasks and retain the old goal. The original 18/24 native versus 6/24 FIR result is a saved numerical batch result, not a universal planner ordering. Its A/B cases share physical histories and differ only in deadline scoring.

## Independent exact reconstruction

critic_exact.py reconstructs derivatives from the truncated fourth-power response, without source or producer imports. Ordinary return reaches acceleration −21/32 at t=77/100 while maximum absolute jerk is 25/4. The far proposal reaches jerk 45/4 at t=23/25 and acceleration −71/72 at t=349/450. Rejecting that proposal leaves the reference exactly 1/25 m from the revised goal after the old tail. The approximately 40 mm actual error remains a numerical physical claim, distinct from this exact reference statement.

At execution 13/25 the old reference q/v/a/j is (77/19200, 23/480, 5/16, −5/4). Dropping history would reset nonzero reference derivatives. A new fourth-order causal pulse has zero derivatives through jerk at insertion and preserves this old prefix. Neither fact permits resetting the actual plant. The 0.51 s deadline precedes delivery/execution 0.52 s, so it fails the declared causal service promise regardless of accidental endpoint coincidence.

Velocity cannot be certified from knot samples alone: v(t)=t(1−t) on [0,1] has zero endpoint velocities but reaches 1/4 at the interior, violating a 1/5 limit. This is a generic polynomial negative control, not a claim that the old implementation omitted interior roots. Its original reference_extrema routine searches those roots numerically; exact acceleration/jerk certificates alone do not certify velocity.

## Independent candidate certificate replay

critic_certificate.py reads the inventor's serialized certificates without importing producer functions. It binds the old event exactly to (time 11/50, displacement 1/50, width 1/5), requires all kernel knots and continuous full interval coverage, checks each degree-four polynomial at five rational points against the independent response formula, and checks its cubic velocity Bernstein identity at four points. Acceleration stationary points and jerk endpoints are reconstructed independently. These finite equality checks establish the respective polynomial identities because the degrees and knot-free intervals are known.

The new return pulse of width 1/4 has reference velocity bounded by 1/15, exact acceleration peak 32521/66075, and jerk peak 689/125. Its tail ends at 1.52 s before deadline 1.70 s. The new far pulse of width 3/10 has velocity bounded by 4/45, acceleration peak 103/211, jerk peak 445/81, and tail 1.72 s before deadline 1.90 s. Old widths, times and signed displacements remain intact. Bernstein velocity bounds are sufficient and need not be exact maxima.

Mutations changing an old width, a polynomial coefficient, removing a phase, or corrupting a Bernstein coefficient all fail the consumer. The initial checker required only the minimal knot set and rejected harmless additional progress/deadline subdivisions; that overstrict first attempt is recorded, and the repaired checker allows subdivisions while requiring every kernel knot and full ordered coverage.

## Independent physical replay

critic_plant.py uses DOP853 in error coordinates, independently of the root's augmented matrix exponential. For e=x−q, it integrates

e''' = −r(800e+60e'+1.5e'') + (r/96−1)j + r w.

It starts from the original zero physical/reference state, applies the disturbance from time zero, carries the error state across every polynomial boundary, and reconstructs physical x/v/a. All twelve new cases (two candidates, rates 80/100/120, disturbances 0/.01) pass the original initial-progress and sampled deadline/remain conditions. Initial progress is approximately 3.11–3.13 mm. Across those cases, sampled post-deadline error is below 12.511 micrometres, speed below 3.5e−7 m/s, and acceleration below 1.21e−5 m/s².

These are independent numerical integrations and dense sampled remain checks, not interval enclosures or all-time plant theorems. A completed reference tail is not itself an endpoint-error proof. No same-distance efficiency or physical energy comparison follows. Both width choices are post hoc research candidates; they require a newly declared paired native benchmark before claiming competitive performance beyond these fixtures.

## Gate

GO for bounded new-event width selection with retained history, complete reference certificates and a separately certified physical task gate. NO-GO for jerk-only admission as the full contract, for treating rejected authority as successful motion, or for silently widening old pulses. HOLD universal admission, all-time physical endpoint/remain guarantees and broad native competitiveness until their respective proofs or declared experiments exist.

Next test: freeze a bounded width-selection rule and candidate set before new reversal cases, bind every certificate to old history and the same authoritative task/deadline, then compare with native planning from each method's actual executed state under the same causal buffer. Include unavailable deadlines, near-boundary acceleration, interior velocity extrema and reference-versus-actual-state mutations. A fallback/rejection must report task failure rather than hide it.

Subjective quality 19/20; not a probability. Exact arithmetic, kernel lemmas, numerical physical evidence and hardware acceptance are separate. No hardware or original-source changes performed.

Independent kernel replay: all ten domain_extrema.lean declarations compile with only permitted axioms. Their source-to-polynomial coefficients are independently checked here, but the Lean file is not a complete finite-history compiler or an ODE theorem. Scoped Python import/style and closure-binding warnings were corrected; no original files were changed.

Final delay review: all four domain_delay.lean lemmas independently compile with permitted axioms. The necessary 0.10 s delay applies only to the declared single new equal-opposite event, fixed width 0.2 s, old event retained and separation parameter alpha in [1.5,2]. It is not a lower bound for other replanning families. The execution at 0.62 s is a newly proposed future timing policy; the original delivery and frozen benchmark remain unchanged. Shifting the buffered reference does not shift the full disturbed physical initial condition.

Independent DOP853 versus PM matrix-exponential comparison agrees on all twelve matching candidate decisions, with maximum endpoint coordinate differences [1.5265566588595902e-16, 1.90585441275004e-15, 7.165860193772281e-15] in SI units. These numerical crosschecks do not establish an interval error enclosure.

Additional scope witness: critic_buffered.py independently integrates the original buffered events (.28,+.02,.2),(.68,−.02,.2) with r=80 and w=.01 from zero physical initial state. DOP853 finds actual acceleration approximately −.500069900945 at t=.8799160401 while reference acceleration is −.499999911884. Thus the original reference acceleration certificate does not ensure the same actual acceleration limit. This is numerical evidence with independent-method support, not a certified physical inequality; the original benchmark correctly used reference bounds and separate physical endpoint tolerances.
