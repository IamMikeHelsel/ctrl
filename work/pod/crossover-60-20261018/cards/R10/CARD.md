# R10 — complete moving-goal admission

AI-written initial review. **GO for bounded retained-history admission; complete physical guarantees and native competitiveness remain open.** Actual timed coverage is in state.json.

## Original question and source

Can retained-history motion admission enforce velocity, acceleration, jerk and task deadline simultaneously during reversal, while competing with native online planning? The frozen source is moving-goal-08/builder/report.txt in the ctrl research notebook. Its hash matches selection. Source packets, piece generation, scalar physical controller and reports were inspected; hashes are saved in source_binding.json and pm_source_hashes.json. No original file was changed.

The source reports18/24 native valid tasks versus6/24 fixed-width FIR tasks, with independent high-precision replay. These are historical scalar-model results. A jerk-only guard admits ordinary return despite exact reference acceleration21/32>.5. Far reversal has proposed reference jerk45/4>7.5, so rejection retains the old+20mm goal against the authoritative−20mm goal. Good tracking of that old reference does not complete the task.

The common source V/A/J contract applies to the reference (.1m/s,.5m/s²,7.5m/s³). Its physical task separately requires initial1mm progress by.5s, causal delivery, deadline tolerances(.2mm,.001m/s,.02m/s²), and sampled remain through2.5s. No reference-to-actual derivative equality is assumed.

## Transfers, tests and invariants

1. **Polynomial certification.** Convert the retained signed-event sum into exact interval polynomials. Jerk is affine; acceleration extrema include its interior stationary point; velocity is cubic and needs interior roots or a sufficient Bernstein enclosure. This preserves full old history. Testing only knots can miss velocity extrema.
2. **Viability and timing choices.** Change only the new event width or prospective execution time, treating limits and deadline as separate predicates. Never rescale the old event or reset physical state. Widening can remove cancellation and increase total jerk, so feasibility cannot be assumed monotone in width.
3. **Unexpected transactional admission.** Treat a new goal as a proposal requiring a complete reference/task certificate before commit. Rejection preserves the old motion but must report task noncompletion; it cannot erase the authoritative goal or earn a smoothness win. A shared certificate interface could evaluate both native and FIR proposals without assuming either generator is universally preferable.
4. **Tracking-margin erosion.** Reference limits and actual plant limits are different. A physical derivative guarantee requires a justified tracking-error reserve. This connects to C02 response enclosures and S12 safety-margin accounting.

## Exact reference evidence

Domain and critic independently reconstruct the original events and recover ordinary acceleration−21/32 at t=.77 and jerk peak25/4. Far candidate acceleration is−71/72 at349/450, with jerk45/4. Source buffered motion has exact acceleration bound.5, jerk5, and sufficient velocity bound1/15. Its21 rational Bernstein rows cover seven intervals and all three derivative limits.

The following two NEW candidates retain the original first event(tau=.22,delta=.02,h=.2) and revision time.52 exactly. They change only the proposed new pulse width; they do not rewrite the frozen benchmark.

| Candidate | New delta | New width | Velocity sufficient bound | Exact acceleration peak | Exact jerk peak | Reference tail | Deadline |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Ordinary return | −.02 | .25 | 1/15 | 32521/66075≈.49218 | 689/125=5.512 | 1.52 | 1.70 |
| Far reversal | −.04 | .30 | 4/45 | 103/211≈.48815 | 445/81≈5.49383 | 1.72 | 1.90 |

An independent consumer reconstructs all required event knots, interval polynomials and Bernstein identities from the original truncated-power formula. It checks interior acceleration extrema, jerk endpoints and deadline reference states, and rejects changed old width, wrong coefficients, omitted phase and wrong Bernstein data. Extra scoring subdivisions are allowed; an initial overstrict checker rejection was corrected and retained. These full reference certificates are exact rational computations. Fourteen Lean lemmas separately check algebraic witnesses, Bernstein bound soundness and the delay-family result; the entire serialized event-to-piece compiler is not a Lean theorem.

A second candidate delays only ordinary return execution from.52 to.62 at fixed width.2. Within the declared equal-opposite, single-revision family and separation range[.3,.4], meeting the acceleration limit requires the full extra.10s. This is a scoped necessary condition, not a global replan lower bound. Its reference tail is1.42; no new physical test of this delayed policy was performed, and the original latency contract remains unchanged.

## Independent physical experiments

Root independently reconstructed the original plant/controller and used augmented matrix exponentials at1ms and.5ms. Critic independently used DOP853 on error coordinates. Both retain the original zero initial physical state and all subsequent state, with disturbance active from time0. The two widened candidates each pass all six original rate/disturbance scenarios (rates80/100/120, disturbances0/.01) for endpoint, initial progress and sampled remain.

For the12 matching scenarios, maximum endpoint disagreements are1.53e−16m,1.91e−15m/s and7.17e−15m/s². Maximum deadline position error is about12.511micrometres; minimum initial progress is3.1119mm. Sampled settling ranges are1.4315–1.432s for widened return and1.630–1.6305s for widened far reversal. These are numerical outcomes, not rigorous enclosures or hardware measurements.

The root also replays unchanged buffered, predelivery and frozen failure controls. Predelivery.51s still fails before revision execution.52s. Frozen ordinary return still fails the reference acceleration gate even though its physical endpoint passes; frozen far rejection still leaves about40.0125mm deadline error. The72 records contain duplicate return/predelivery physical histories and two resolutions; they are not72 independent motion scenarios. See pm_physical.json and pm_summary.json.

A material physical-limit counterexample appears in the unchanged buffered case: at rate80,w=.01, independent numerical extremum search gives actual acceleration magnitude≈.500069900945 near t=.87991604, although reference magnitude≈.499999911884. Thus passing the source reference gate does not establish actual acceleration≤.5. The widened candidates have sampled physical margin, but an all-time actual derivative guarantee remains unproved.

## Failures and scope checks

- A distinct cancellation fixture has jerk peak3/8 with new width.2 but679/128 with width.4. Wider alone is not a monotone safety improvement.
- Changing the old width changes already executed q/v/a. A global time rescaling is an invalid retained-history repair.
- New width.3 for ordinary return ends its reference tail at1.72, later than deadline1.7, yet its reference endpoint tolerances already pass. Tail-before-deadline is sufficient, not necessary, and neither direction by itself proves the physical task.
- Shifting a reference trace does not shift a physical trajectory initialized under disturbance at time0.
- Native documentation describes V/A/J-constrained online state-to-state generation; neither that claim nor the historical comparison supplies a physical tracking theorem for this plant. Primary links are in pm_sources.md.

The triangle-inequality physical bridge has explicit targets: sufficient tracking-error reserves for return are(1/30,1033/132150,497/250) in velocity/acceleration/jerk units; for far reversal they are(1/90,5/422,325/162). These are exact remaining reference margins, not established tracking-error bounds. Proving those error envelopes is a precise next obligation; buffered reference acceleration has zero such reserve.

## PM decision

**GO**, after all60 initial reviews, for a bounded width-selection and complete-certificate experiment. Twenty new timing/goal cases, a discrete rational width list and mandatory failure controls are frozen in next_block_protocol.json. Generate a fresh paired native comparison with identical authoritative packets and each method's own retained executed state. Report reference, actual derivative, endpoint, remain and causal-service predicates separately. Use exact certificates and physical enclosures before claiming all-time guarantees. Numerical paired scores may be reported at their actual evidence level.

The tested repair changes what to try next: retained-history FIR need not be limited to its failing fixed-width jerk guard. It does not establish arbitrary replanning, multi-axis/contact dynamics, optimality, energy advantage, native competitiveness or physical robot acceptance. No new native benchmark was run here, and no historical count was relabeled as new evidence.

Review quality: faithfulness4, reproducibility4, discriminatory value4, independent critique4, actionability3 = **95/100**. Subjective confidence is high for scoped exact certificates and reproduced numerical outcomes; general usefulness and physical guarantees remain unestablished. All four roles used the inherited working model, exact runtime ID unavailable; no model-family diversity or Spark inference is claimed.
