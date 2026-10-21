# R10 cross-discipline inventor

AI-written research; inherited root model, exact model identifier unavailable. Root owns elapsed timing and the PM decision. Only R10 inventor artifacts changed. No original source, frozen experiment, native binary, hardware, or remote resource was modified.

## Question, source and comparison boundary

Can retained-history motion admission enforce the full velocity/acceleration/jerk reference limits and the original task deadline during reversal, while competing with native online planning?

Read the R10 card and `/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/moving-goal-08/builder/` files `report.txt`, `packets.json`, `make_references.py`, `knot_check.py`, `reference-extrema.json`, and the actual scalar controller in `run_comparison.py`. No original script was imported or executed. Some source entry-point counts/older assertions differ from the final report; this role does not claim to have regenerated that frozen batch. The report's native18/24 versus FIR6/24 is historical independently replayed numerical evidence, not a new experiment here.

The frozen FIR uses width h=.2 for every accepted step. First event: time .22, displacement +.02. Revision at .52: displacement −.02 for the ordinary return, or −.04 for the far reversal. The complete signed old event remains. Common reference limits are |q'|≤.1, |q''|≤.5, |q'''|≤7.5. Physical deadline tests are separate: position error .0002, speed .001, acceleration .02, with the original remain/progress obligations. These reference limits are not automatically bounds on actual physical velocity, acceleration or jerk.

The original ordinary-return curve violates acceleration exactly at21/32. The original far proposal violates jerk45/4 and is rejected, so its executed frozen baseline keeps the old +.02 goal. When our script evaluates the two-event far curve at h=.2, it labels it a **counterfactual rejected proposal**, not the executed baseline.

## Three transfers

**1. Causal memory and local time scaling.** The four-box reference is a linear sum of signed step responses. Preserve every old event, including its width and unfinished tail, and widen only the newly arriving event. The added quartic step and its first three derivatives vanish at its start, so this retains the entire past and joins q,q',q'',q''' continuously without resetting physical state. It trades future duration for a different derivative profile while preserving the authoritative final target.

This is a new candidate architecture: per-event widths replace the frozen common-width FIR rule. It is not a retrospective repair of its benchmark. A falsifier is any change in the old executed prefix, or a summed derivative exceeding a limit even when each individual event looks acceptable. Global retiming is forbidden by the retained-history condition: changing the old width .2→.25 changes q/v/a at t=.5, before the .52 revision.

**2. Deadline scheduling as a constrained smoothing budget.** A new event's exact completion time is tau+4h_new. For completed-tail service, the deadline supplies an upper width cap, while derivative limits push toward wider kernels. For these timestamps the completed-tail caps are59/200 for return and69/200 for far reversal. The tested widths were declared in advance:1/4 and3/10, respectively. Both leave .18 seconds between final reference tail and deadline.

The cap applies only to **exact tail completion**, a sufficient reference condition. It is not necessary for the original tolerance-based physical deadline. In fact return h_new=.3 finishes at1.72, after deadline1.7, but its reference deadline state is exactly q=1/60750000, v=−1/303750, a=1/2025, all within the original endpoint tolerances. Physical acceptance still needs the actual plant response and remain checks.

Nor is widening monotone for a superposition. A separate causal cancellation fixture, old event(.22,+.02,.2), new event(.23,−.02,h), has summed jerk peak3/8 at h=.2 but679/128 at h=.4. Widening weakens cancellation and increases the peak. Thus an admission algorithm must check the full retained-history curve for each proposed width; it cannot blindly binary-search a presumed monotone feasible set.

**3. Unexpected transfer: a proof-carrying transaction shared by different planners.** Separate candidate generation from the acceptance decision, as a transaction whose effects are checked before commitment. Native planning and FIR shaping may propose different futures, but each proposal must bind the accepted history, current execution state, authoritative target, readiness/commit times, full motion limits and deadline evidence. The checker accepts a candidate only against those same objects. Rejection must report that the new task remains unmet; continuing toward the old target does not become a successful smooth reversal.

For polynomial references, rational piecewise coefficients support a common constraint language even though native exports and rational FIR have different numerical provenance. A common checker must respect exact binary export origins and reconstruction allowances for native data instead of claiming its floating coefficients are already a physical theorem. Required falsifiers include a changed old-event width, a certificate generated for a different target/deadline, jerk-only acceptance despite acceleration excess, and reporting an effort win for an invalid task. This transfer proposes a common acceptance boundary, not universal replacement of the native planner.

## Exact reference experiment

`inventor_width.py` represents each event with its own rational width and expands the summed truncated-quartic expression on every combined knot interval. It exports local derivatives [q,qv,qa,j,snap] at each left endpoint. Exact knots include all event boundaries, .5 progress time, the task deadline, and the2.5-second horizon.

Jerk is affine on each piece, so endpoints certify its exact peak. Acceleration is quadratic, so endpoints and rational zeros of jerk certify its exact peak. Velocity is cubic; exact Bernstein coefficients give a sufficient upper bound, not necessarily the exact maximum. Adjacent pieces are checked for equality through jerk; final constant tail, target equality and zero derivatives are checked exactly. Old-prefix equality is algebraic because the new step is zero before its event; explicit probes also check it.

| candidate | sufficient velocity bound | exact acceleration peak | exact jerk peak | final tail / deadline |
|---|---:|---:|---:|---|
| frozen ordinary return h=.2 |1/15|21/32 (fails)|25/4|1.32 /1.7|
| new return, only new h=.25 |1/15|32521/66075 ≈.49218|689/125 =5.512|1.52 /1.7|
| rejected far proposal h=.2 |2/15|71/72 (fails)|45/4 (fails)|1.32 /1.9|
| new far reversal, only new h=.3 |4/45|103/211 ≈.48815|445/81 ≈5.49383|1.72 /1.9|

Both predeclared new candidates pass all three reference limits and exact tail completion before the original deadline. Their entire first event remains unchanged. Their final targets are exactly0 and−1/50, with zero final q'/q''/q'''. This establishes explicit reference feasibility where the frozen adapter fails; it does not yet establish all physical task checks or comparative effort.

`inventor_failures.py` saves the exact monotonicity counterexample, the altered-old-prefix values under invalid global rescaling, and the wider-than-tail-cap endpoint-tolerance example. These are deliberately separate scope tests, not additional tuned candidates in the frozen comparison.

## Physical and comparative acceptance

The root independently propagated the exact piece exports with a matrix exponential at rates80,100,120 and disturbances0,.01, with the original controller and zero initial physical state, no reset at revision, unchanged deadlines and2.5-second horizon. Its24 records for these two candidates (12 scenarios, two sample spacings) pass endpoint, sampled remain, initial progress and causal service. Maximum absolute endpoint error is approximately12.511 micrometres; minimum initial progress is3.1119 mm. The critic independently obtains the same acceptance using DOP853 in error coordinates. These physical results belong to `pm_physical.json` and `critic_plant.json`, not an inventor integration or all-time proof. The separate predelivery-deadline negative control must not be pooled with the two candidate successes.

The new reference results must not overwrite the native18/24 or FIR6/24 baseline. A fresh candidate comparison must keep the same packet readiness, execution buffers, task constraints and actual-state carry. Since different methods can be at different physical distances from the revised goal when it arrives, jerk-squared or command-variation comparisons alone do not show energy efficiency. Native and shaped reference performance can trade duration against effort; no universal dominance follows from these two candidates.

## Gate

**GO** for bounded, history-preserving variable-width admission with the full reference gate and a separately checked physical deadline/remain bridge. The critic independently replayed the rational reference certificates and rejected changed-history, coefficient, phase-coverage and Bernstein mutations. Root and critic physical replays pass the unchanged sampled task checks. Next: freeze a bounded width-selection rule before new cases, then compare with the saved native cases using the original scoring. A subsequent acceptance adapter should reconstruct coefficients from bound event history and reject a changed-prefix certificate, rather than merely trusting an exported bound.

**NO-GO** for jerk-only admission, rescaling old events, assuming widening monotonically improves the sum, or treating reference tail completion as the exact physical task definition. **HOLD** all-time physical guarantees, arbitrary replans, multi-axis/contact behavior, and universal native replacement.

Evidence: exact rational reference computations and failure witnesses, plus independently attributed numerical physical replays; not an inventor Lean proof or hardware validation. Both own scripts pass Ruff. Quality: faithfulness4/4, reproducibility4/4, discriminatory value4/4, critique4/4, actionability3/4 =19/20 (95%). Subjective confidence is high in the reference calculations and these numerical fixture outcomes; all-time physical acceptance and comparative advantage require separate evidence.
