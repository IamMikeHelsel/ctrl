# S12 independent critique

AI-written by independent critic; inherited root model, exact runtime model identifier unavailable. Original question: can one justify an action while source attribution remains ambiguous and observations share duplicated information? The answer is conditionally yes for the recovered static scalar model. A dynamic or physical safety claim remains unproved.

## Original contract and existing evidence

Read source-attribution/{challenge.txt,model.json,check.py} and adjacency-review/coupled-measurements.txt under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/`. No new literature or novelty claim is made. The latter document's citations are historical source summaries, not fresh full-paper reviews.

The pinned model is signed real scalar, wheel gain exactly1, w/d in[-2,2], shared q=lambda*d with lambda in[1/5,3/10], baseline w+d=1±1/10, separating w+q=5/8±1/40, and held-out function w+q/2 with observation9/16±1/40. Trial mass changes only w by known1/2, and the correction changes w to w+c while leaving d and transfer unchanged. These are model assumptions, not identified vehicle facts. Both candidate corrections were predeclared as-1/2 and-1. Acceptance requires |w+c|<=1/8 and |w+c+rho*d|<=3/4 for every retained tuple and rho in[0,1]. Held-out data are not used for identification in the original artifact.

`critic_original_replay.py` freshly checked the pinned model hash and replayed the existing independent certificate checker:56 endpoint bounds,1 infeasibility certificate,8 action evaluations. Five corruptions were rejected: missing sign branch, missing action, changed held-out result, wrong correction decision, and negative dual weight. Original checker uses assertions and its CLI explicitly refuses Python-O; importing its verifier does not itself pin the model file, so this replay performed the hash check separately. No source files were modified.

The original checker already enforces nonempty retained sets, complete stage/branch/action coverage, and a single surviving convex branch before using scalar projection interval overlap. There is no demonstrated existing hull-compatibility bug in that fixed checker. Its ordinary Python/Fraction implementation remains trusted; replay is not a Lean proof.

## Failure cases that a generalization must reject

`critic_cases.py` constructs exact rational diagnostics:

- Worlds in[-2,-1] union[1,2] have hull[-2,2]. Observation[-1/4,1/4] intersects the hull but no actual branch. Outer hulls can justify universal bounds conservatively; they cannot establish an existential compatibility witness.
- Worlds theta=-1,+1 each admit a different correction keeping |theta+c|<=1/2, but their safe correction sets[1/2,3/2] and[-3/2,-1/2] do not intersect. `for every world there exists an action` is insufficient; one executable action must work for every still-indistinguishable world. A policy must select the same action for worlds with the same observation history.
- A universal bound over an empty set evaluates true, so operational acceptance needs a nonempty guard. Inconsistent data invalidate this evidence/model combination; they do not certify arbitrary actions or prove that no independent fallback exists.
- Four identical readings with shared error can retain truth theta1,error-1. Halving a deterministic error interval using a standard-error rule excludes that truth. Exact duplicated constraints are idempotent. Merely replacing shared bounded errors by separate bounded-error coordinates creates an outer set and is conservative; it is not itself a false-confidence mechanism.

A further joint-observation diagnostic: the single convex set x+y=1 in[0,1]^2 has each scalar projection compatible with observation0, yet the joint observation(0,0) is impossible. The one-convex-branch condition validates scalar interval projection only; independent overlap of multichannel marginal intervals does not suffice.

The inventor's baseline-stage joint-hull example is also correct: feasible source worlds(1/2,1/2,1/10) and(3/2,-1/2,-3/20) have midpoint(1,0,-1/40), violating q=lambda*d because d0 demands q0. Added observations d0,q=-1/40 are a hypothetical joint diagnostic, not available original sensor rows. The source-law relation, joint error identity, and retained branches must survive updates together.

## Independent precision-to-action check

`critic_design.py` does not import producer functions or trust vertex enumeration. It verifies seven serialized experiment rows, their explicit feasible endpoints, the action envelope, and four corruption controls. It independently derives global wheel bounds using nonnegative linear combinations of the model rows:

`w_min=(59/200-epsilon)/(7/10)`, `w_max=(89/200+epsilon)/(4/5)` for0<=epsilon<=1/10.

For the upper bound, add the separating upper row, q>=d/5, and1/5 times the baseline lower row. For the lower bound, add the separating lower row, q<=3d/10, and3/10 times the baseline upper row. The negative-d branch is impossible because w+q>=w+3d/10>=9/10, exceeding5/8+epsilon. Explicit endpoint worlds attain both bounds and satisfy the full prior and shared leakage relation.

At the original epsilon1/40, the complete continuous safe correction interval is[-143/280,-37/80]. The wheel width is151/1120+(75/28)epsilon. Some common correction exists iff epsilon<=43/1000, whereas the predeclared correction-1/2 requires epsilon<=13/400. At epsilon43/1000 the unique correction is-97/200 with wheel range[9/25,61/100]. The mixed-response constraint remains satisfied. This is prospective design analysis with a continuous action-set extension; it does not change the frozen observations or authorize new corrections.

The false-confidence probe-23/50 is outside the original action list and is explicitly a diagnostic. The original retained tuple(47/80,5/16,1/16) gives corrected wheel residual51/400>1/8, while illegally halving the baseline error bound excludes that tuple and falsely accepts the probe. This demonstrates a concrete action-level failure, not just excess numerical confidence.

## Kernel evidence and limits

Independently compiled domain_guarded.lean and domain_gap.lean with the repository's pinned Lean environment. Seven generic logical declarations use no axioms; four rational gap declarations use only propext,Classical.choice,Quot.sound. Logs are critic_guarded_lean.log and critic_gap_lean.log. No approved Challenge was changed, and these are isolated research theorems rather than solutions bound to an approved Challenge.

The generic theorems establish conditional truth retention, duplicate idempotence, nonempty guarded acceptance, conservative outer-set universal bounds, and joint witness logic. `Safe` is an uninterpreted predicate; physical containment and runtime branch enumeration completeness remain hypotheses. The gap example is a declared baseline-stage extension with1/2<=|d|<=1 and changed held-out interval[19/20,21/20]. It omits the original separating row: its two witnesses fail that row. The held-out function is preserved, not the old held-out data. The domain worker corrected this scope wording after review.

## Recommended gate

GO for a bounded, provenance-preserving action-certificate experiment and prospective precision-to-action design. NO-GO for existential claims from a hull, per-world action selection hidden behind a common observation, duplicate-driven deterministic error shrinkage, or dropping unverified branches. HOLD physical stopping/robot claims until a dynamic model, bounded sensor/phase errors, intervention-induced transfer changes, executable action policy, and safe termination are specified and connected to the evidence contract.

Quality rubric: faithfulness4/4, reproducibility4/4, discriminatory value4/4, critique4/4, actionability3/4:19/20(95%). Subjective confidence is high in the fixed-model logical conclusions and low in physical transfer; this is not a calibrated success probability. No novelty or hardware acceptance is claimed.

### Original static numerical contract kernel check

Independently compiled the later domain_original_action.lean successfully. All four declarations use only propext,Classical.choice,Quot.sound. Checked source binding: real-valued worlds,1/5<=lambda<=3/10, q=lambda*d, baseline[9/10,11/10], separating[3/5,13/20], correction interval[-143/280,-37/80], rho in[0,1], and both original static limits. Omitting the box priors in the sufficient theorem strengthens its conclusion; feasible endpoint worlds separately satisfy those priors. The trial reading follows the baseline interval after its known1/2 offset. Held-out information is correctly absent from the identification assumptions. Endpoint necessity plus sufficient action theorem supports the exact static action interval. The statements remain isolated research theorems, not approved Challenge solutions or a dynamic stopping proof.

Audited SHA256 hashes: domain_guarded.lean `a6a9312f307832f0719c4df4ae3b9293c0cdc71fb2a711f6f4d582a636762524`; domain_gap.lean `9d36ebb99e40b4c530608cc142fb85e6c044492d13ccdd278d539d30625b8cbc`; domain_original_action.lean `be7e8b8db344b48c1363de25ce56b594892781a4f83bb8e92c14e586e1ba5eee`. Original-action compilation log: critic_original_action_lean.log.

Provenance must preserve both event identity and the declared error-sharing map. Two equal bounded constraints are redundant even if from distinct events, but equal observations do not establish a common latent error. A repeated event identifier with a changed payload or calibration cannot silently overwrite the retained evidence. Hashing a constraint does not justify nuisance cancellation or source invariance.

### Decision coordinates and the boundary of useful compression

`critic_coordinates.py` independently checked the inventor's coordinate result using the original, previously verified support certificates. A Cartesian(w,d) box gives false rejection of correction-1/2 because its artificial corner produces449/560>3/4. The alternative coordinates(w,b=w+d) retain exactly the four support values queried by the frozen acceptance predicate. For every individual world, `w+c+rho*d=(1-rho)(w+c)+rho(b+c)`; universal rho in[0,1] safety is equivalent to safety at the two endpoints. The resulting mixed range is[-4/35,3/5], and the exact safe correction interval remains[-143/280,-37/80]. This compression is exact for the specified decision predicate, not for arbitrary queries or future evidence updates.

The decision box has a nonphysical corner: w27/70,b9/10 gives d18/35. Shared leakage implies q<=27/175, so w+q<=27/50<3/5, contradicting the original separating observation. Thus joint observations pinning that corner must be rejected using the underlying joint model even though the decision summary contains the corner. These hypothetical future joint readouts are not the original held-out sensor or an actual measurement.

The precision threshold also conditions on the observed center5/8. A changed perfect separating readout-3/10 admits original-prior/baseline worlds(-9/10,2,3/5) and(-3/5,3/2,3/10), with respective leakage3/10 and1/5. Their wheel contributions differ by3/10, larger than the1/4 range compatible with a common1/8 wheel-residual bound. No common correction exists despite zero measurement error. This is explicitly changed data, not a refutation of the threshold derived for center5/8. Precision alone cannot guarantee that every possible future readout permits an action.

A reusable receipt needs verified nonempty new-world-set inclusion in the old world set and unchanged action/predicate semantics. Event identity, error-sharing assumptions, calibration, source/transfer invariance, and—when generalized dynamically—state snapshot/time/horizon must remain bound. An unchanged model name and action are insufficient if state advances or the uncertainty set expands. This is a design obligation, not an implemented physical safety guarantee.

Independently compiled final domain_decision_box.lean: six declarations use only propext,Classical.choice,Quot.sound. The abstraction theorem explicitly requires containment and attainment of all four marginal endpoints, which also ensures nonemptiness; it does not certify a runtime summary producer. SHA256 `6351edfed20f0f2458ff2e6ee27563d14cab65ae80cedde3213250dda3a6f32b`; compilation log critic_decision_box_lean.log. Four critic Python scripts pass scoped lint and formatting checks.

`critic_pairs.py` independently checks stronger changed-readout action conflicts. At perfect separating center3/10, two valid source-prior/baseline worlds each permit a correction, but their individual safe action sets are distinct singletons{-1/4} and{-13/80}. Both remain compatible with the hypothetical half-leakage observation61/320±1/40, including the equality boundary at error7/320; distinguishing these two predicted intervals requires error strictly below7/320. The baseline-row pair threshold is strictly below7/160. This is pair discrimination only, not full feasible-set safety.

At changed center2/5, two retained worlds have non-singleton individual safe intervals[-73/200,-29/100] and[-57/200,-21/100], separated by1/200. Thus the action-quantifier failure is not merely a singleton-boundary artifact. Their prospective baseline prediction intervals separate at error strictly below1/25. Both diagnostics alter the separating readout; the first also alters held-out center. They do not modify or refute the original saved observations. Five critic Python scripts pass scoped lint and formatting checks.

### Confusability theorem audit

Audited pm_confusability.lean independently. Worlds A=(6/25,4/5,4/25) and B=(4/25,4/5,6/25) satisfy the original priors, baseline interval and leakage relation, with explicitly changed perfect separating readout2/5 and held-out center3/10. Corrections-1/3 and-1/4 respectively satisfy both static limits uniformly over rho. A common correction would require c<=-29/100 from A's rho1 endpoint and c>=-57/200 from B's wheel bound, an impossible gap1/200. Their held-out predictions8/25 and7/25 differ1/25; error strictly below1/50 separates those two predicted intervals. This does not establish full-posterior safety or a physical measurement guarantee.

The independent compile passed all four pm_confusability declarations with only propext,Classical.choice,Quot.sound. SHA256 `cf7d345cc1bd38070944d9e59ceab331975c7637b5fa6161279bfca356f77ada`. The isolated negative-control copy critic_false_confusability.lean changes one exact separating equality from2/5 to3/5. It correctly fails compilation(exit1, unsolvedFalse); its failed declaration reports sorryAx and is rejected, never accepted as proof. Both logs are retained. The original root file was not changed.
