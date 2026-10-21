# S12 inventor: certify a common action before identifying every cause

AI-written; inherited root model, exact runtime identifier unavailable. Sources inspected: frozen S12 card, campaign charter, original source-attribution challenge, coupled-measurements review, model.json and experiment.py. No source artifact edited. Fresh results are exact Fraction computation and ordinary algebra, not Lean, dynamic stopping or hardware evidence.

The original static model keeps one joint tuple(w,d,q), q=lambda*d, lambda∈[1/5,3/10], w,d∈[−2,2]. Baseline and known-offset trial constrain the same w+d. Separation constrains w+q. The action must satisfy both |w+c|<=1/8 and |w+c+rho*d|<=3/4 for every retained tuple and rho∈[0,1]. Original declared actions−1/2 and−1 remain unchanged. Extra diagnostic corrections and hypothetical sensors below are explicitly labeled.

## Four bridges and discriminators

1. **Epistemic logic and decision equivalence.** Observationally indistinguishable worlds need not agree on w, but an implementable action must be one common c for every retained world. Map the joint feasible set to the intersection of its safe-action sets, not to a preferred explanation. The distinction is `exists c, forall world` versus `forall world, exists c`. Original baseline worlds(.5,.5,.125) and(1,0,0) share the same baseline/trial values yet need disjoint wheel-correction intervals. Their own suitable corrections do not give an observation-based common policy. Cheap test: compute the full correction interval after separation; it can be nonempty while w remains an interval.

2. **Unexpected: database joins and abstract interpretation.** Shared source/leakage variables are join keys. Projecting channels independently or convexifying before a joint consistency update can invent a tuple. Preserve the exact sign branches for consistency; allow outer abstractions only with the correct one-sided claim. Cheap test: two valid original worlds have a convex midpoint with d0,q!=0, violating the original physical relation. Crucially, convex hull is not automatically unsafe for the present universal affine-action bounds: the sup of |affine| over a hull equals its sup over the generating set. Existential compatibility and universal action validation need different approximation rules.

3. **Idempotent provenance and proof-carrying transactions.** Repeating a deterministic constraint is set intersection with itself; it must not count as new confidence. Model/error/phase identity matter, not packet count or a new message UUID. Bind an action certificate to the joint relation, declared uncertainties and nonempty witness. A certificate transfers to a smaller retained set only if the same response law and true-world-preservation assumptions survive. A changed support/load model is not merely another measurement update. Cheap test:100 duplicates leave the original set unchanged, whereas pretending four copies halve a deterministic error bound falsely accepts a diagnostic correction.

4. **Decision-focused experimental design.** Optimize the next measurement for a common safe action rather than unique source recovery. Map a certified separating-error radius to the width of the feasible wheel interval and then to correction feasibility. Cheap test: derive the exact error threshold at which the common action interval disappears. This yields a concrete acquisition requirement without pretending extra baseline copies identify the source. It remains a static design calculation; the safety and realizability of acquiring the separating condition require a new dynamic model.

## Fresh exact reproduction and negative controls

`inventor_exact.py` independently builds both sign-branch halfspace systems from the original model and enumerates rational vertices. It does not invoke the old generator. Vertex enumeration and the new checker code remain trusted in this evidence tier.

- Baseline wheel range is[−11/10,2]; no correction meets the wheel limit uniformly.
- One hundred exact duplicate baseline observations leave the joint vertex sets unchanged. The known trial offset makes its constraints identical to baseline, as expected for assumed wheel sensitivity1.
- Separation gives wheel range[27/70,47/80]. The entire common correction interval is

      [-143/280, -37/80], width27/560.

  Original c=−1/2 passes, c=−1 fails. Nonunique source attribution coexists with an exact nonempty action set.
- The original held-out prediction is[69/140,99/160], wider than the observed[43/80,47/80]. The sets intersect, but not every retained world predicts that observation. It is compatibility only.

### Joint hull diagnostic, with its scope made explicit

Original feasible worlds are

    a=(1/2,1/2,1/10), b=(3/2,−1/2,−3/20).

Their midpoint(1,0,−1/40) belongs to their convex hull, yet q=lambda*d requires q0 when d0. A hypothetical extra joint observation d0,q−1/40 therefore intersects the hull while both exact sign branches are empty. The actual original scalar held-out sensor does not supply that extra observation; this is an abstraction test, not a newly discovered failure of the saved experiment.

The original baseline union is connected through d=q=0, and the separated set has only one surviving convex branch. Consequently a disjoint scalar-projection gap cannot honestly be asserted for that original held-out instance. The roster's suggested disjoint-hull example needs an explicit extension or a different problem instance.

Empty branch union returns MODEL_DATA_INCONSISTENT and blocks certification. It does not pass every action by vacuous universal quantification. A nonempty set with an empty action interval is a distinct result: evidence consistent, no common admissible correction under this contract.

### Duplicate-confidence falsifier

Deliberately replace baseline error1/10 by1/20 as though four duplicate copies justified statistical shrinkage. With the unchanged separating observation, this wrong set accepts diagnostic c=−23/50. The original retained world

    (w,d,q)=(47/80,5/16,1/16)

has wheel residual51/400>1/8=50/400 after that correction. Thus the false-confidence step can cause a concrete wrong acceptance. This diagnostic c is not one of the original two declared actions and is not executed. The original outcomes remain unchanged.

## Exact measurement-precision design threshold

`inventor_design.py` varies only the prospective guaranteed error radius epsilon of the separating observation centered at5/8; baseline uncertainty remains1/10. This is a design analysis, not permission to shrink the error attached to existing data. Restrict0<=epsilon<=1/10.

Let b=w+d∈[.9,1.1] and a=w+lambda*d∈[5/8−epsilon,5/8+epsilon]. Since a<b throughout this range,

    w=(a−lambda*b)/(1−lambda)

increases with a, decreases with b, and decreases with lambda. Therefore exact extrema are

    w_min=(59/200−epsilon)/(7/10),
    w_max=(89/200+epsilon)/(4/5),
    width=151/1120+(75/28)*epsilon.

The formulas' endpoint witnesses satisfy the unchanged priors and shared-leakage relation. The negative-d branch is impossible because it would imply a>=b>=.9, whereas a<=.725. Hence the formulas cover the full feasible set, not a favored branch. The original mixed-response condition is weaker than the wheel interval constraints throughout the potentially feasible correction range.

A common correction exists exactly when wheel width<=1/4, namely

    epsilon <= 43/1000.

The original fixed correction−1/2 needs the tighter epsilon<=13/400. At epsilon43/1000 the sole common correction is−97/200, with wheel range[9/25,61/100]. This is an analytical candidate for prospective design, not an extra accepted action in the frozen experiment. Exact tests at seven radii include both boundaries and failures immediately beyond them, with feasible extremal tuples saved.

The useful research direction is now measurable: obtain a justified separating observation with error below the action threshold, while retaining the joint transfer assumptions. Unique wheel/drivetrain attribution is unnecessary for this static decision, and duplicated common information cannot substitute for the separating measurement.

## Gate recommendation and remaining bridge

GO for a bounded proof-carrying static measurement-to-action prototype: carry complete branch coverage, exact nonemptiness, idempotent constraints and a common-action interval; distinguish inconsistency from insufficient action information. The novel claim is not source separation or robust control—those are established methods. This session supplies a precise small test and an explicit decision-focused threshold.

HOLD any robot stopping or balancing-safety transfer until there is a dynamic intervention/measurement model with phase/quadrature, changing support, disturbance and actuator assumptions. The current static acceptance formulas do not establish an acceleration-target bound, response-rate bound, physical transient or safe execution protocol.

## Follow-up: decision coordinates remove unnecessary attribution

`inventor_coordinates.py/json` preserves the original data and action. The exact source-coordinate marginal box is w∈[27/70,47/80], d∈[5/16,5/7]. Treating these as independent gives the fictitious mixed upper value 47/80+5/7−1/2=449/560>3/4 and rejects the original safe correction −1/2. This is conservative loss of usefulness, not unsafe acceptance.

Change representation to (w,b=w+d). The exact ranges are w∈[27/70,47/80], b∈[9/10,11/10]. For each world, w+c+ρd=(1−ρ)(w+c)+ρ(b+c). The triangle inequality bounds the absolute value by the maximum of the endpoint absolute values; evaluating ρ=0 and ρ=1 proves equality. Hence four support values (min/max w and min/max b), together with the nonempty guard, are a lossless abstraction for the frozen acceptance predicate on every joint feasible set. They reproduce the full common-action interval [−143/280,−37/80]. For c=−1/2 the mixed range is [−4/35,3/5], safely within ±3/4.

This transfers predicate-directed abstract interpretation into attribution: keep the full joint branches as the belief state for consistency and updates, while exposing only a small exact decision certificate. The certificate does not establish attribution and is not sufficient for arbitrary future observations. The exact script is an independent rational fixture plus elementary algebra, not a Lean theorem or hardware evidence.

## Follow-up: a decision summary cannot replace the update state

`inventor_update_boundary.py/json` tests the original-data corner (w,b)=(27/70,9/10). Both marginal endpoints belong to the decision box, but together they imply d=18/35 and q≤27/175. Hence w+q≤27/50<3/5, contradicting the original separating observation. The exact joint update is empty; independent marginal compatibility would accept a phantom world. This establishes the paired architecture: full joint branches for updates; four supports for this decision predicate.

The prospective ε≤43/1000 threshold is conditional on separating readout center **5/8**, original baseline center1±1/10, original priors and safety limits. It cannot guarantee an action for every readout. With a perfect separating readout at a changed center +3/10, two retained worlds are A=(1/8,7/8,7/40) and B=(3/80,7/8,21/80). Their baseline predictions are 1 and73/80, respectively. Each individually permits exactly one safe action, −1/4 or−13/80; the intersection is empty. This is an information conflict, not an inherently uncontrollable individual world. The half-leakage heldout predictions are17/80 and27/160. A hypothetical heldout center61/320 is compatible with both at the original error bound1/40. Even reducing that error to7/320 retains both at the midpoint; a strictly smaller error is required to separate this pair's prediction intervals. This is a necessary pair-discrimination target, not a sufficient full-set safety guarantee. Both readout centers are changed diagnostics; original sensor rows and error guarantees are respected.

A second changed-center pair shows the failure persists away from singleton action intervals. At separating center2/5, A=(6/25,4/5,4/25) and B=(4/25,4/5,6/25) yield individual safe-action intervals [−73/200,−29/100] and[−57/200,−21/100], separated by1/200. With common d∈(35/44,7/8], λ endpoints1/5 and3/10, and any center admitting both baseline predictions, the action-interval gap is(11/10)d−7/8>0. The existing baseline row predicts26/25 versus24/25 in the displayed case; justified prospective error<1/25 would distinguish this pair. Repeating shared observations does not justify that precision.

For comparison, perfect separating center−3/10 retains (−9/10,2,3/5) and(−3/5,3/2,3/10). Their wheel gap3/10 alone forbids a common action, but each world also individually violates the possible combined safety range because d>7/8. The positive-center pair is the cleaner attribution counterexample. All these diagnostics preserve nonempty guards; none changes the original accepted observation or original action result.
