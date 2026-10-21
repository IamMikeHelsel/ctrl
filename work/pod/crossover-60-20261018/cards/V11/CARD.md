# V11 — outlier admission in information filtering

AI-written initial review. **GO for a complete, provenance-bound admission checker; current prototype is not accepted.** Timed completion is recorded separately in state.json.

## Original question and provenance

Can a geometric outlier-rejection rule preserve a stated estimation-error bound when combined with an additive information update? The frozen vision survey supplies a proposed connection, while `/Users/mike/Dev/ctrl-research-notebook/ControlsLean/Estimation/InformationFilter.lean` supplies inverse identities in an arbitrary associative ring. Both frozen hashes match; snapshots and source_binding.json are saved here.

The source theorem proves Kalman-form and information-form expressions are mutual inverses under explicit inverse premises. It has no actual state, estimated mean, observation/noise process, positivity, inlier predicate or truth-bearing error bound. Source prose about optimal variance is not itself a formal stochastic theorem. Root compiled byte-identical InformationFilter and ScalarKalman copies in the existing ctrl toolchain and audited all10 InformationFilter declarations: no axioms beyond propext (symmetry uses none). This preserves the algebra; it does not establish a probabilistic interpretation. The original notebook environment was not replayed.

## Three different transfers

1. **Set-membership and support bounds.** Carry the set of all states compatible with justified prior/measurement assumptions. An information update proposes a center; a separate certificate bounds its error over that entire set. This preserves actual truth containment. Nonempty intersection alone proves only compatibility and cannot label a measurement truthful.
2. **Error-correcting redundancy.** Keep every hypothesis allowed by a bound on bad original observations. Geometric redundancy can exclude inconsistent branches, making some residual bounds hold in every remaining world. Repeated copies of one origin do not provide independent fault redundancy. The actual fault budget is an assumption, not something consistency proves.
3. **Unexpected proof-carrying abstention and margin budget.** With only a prior interval of radius a, moving its center by d has sharp worst-case error a+|d|. Preserving the same already-tight bound forces d=0 unless new truth-bearing constraints are supplied. Allowing a larger declared margin permits bounded displacement; it does not justify silently retaining the old bound.
4. **Selection and correlation audit.** Treat admission as a conditioning operation and measurement reuse as shared evidence. Ordinary covariance algebra can remain exactly true while its interpretation for accepted observations fails. This is an epistemic/model issue, not a matrix-inversion defect.

## Discriminating results

The scalar gate is exact: for a nonempty feasible interval[L,U], candidate c has error≤E for every feasible state iff c−E≤L and U≤c+E. Both interval endpoints matter. Two actual bounds intersect soundly, but mere intersection does not prove the true state lies in the new strip.

A valid bounded-noise example uses prior center0/radius1, observation1/2/radius1/10, true state3/5, P=1,R=1/100. The information mean is50/101. Its sharp error radius is53/505 over[2/5,3/5], and its squared error exceeds reported covariance1/101. Valid hard noise bounds alone do not identify covariance with a deterministic squared-error limit.

The declared linear geometry has rows(x,y,x+y,x+2y), observations(1,0,0,0), prior[-1,1]^2, inlier error≤epsilon and at most one arbitrary bad original row. For0≤epsilon<1/4, all three-inlier branches containing row1 are contradictory. The surviving row234 bounds imply |x|≤2epsilon and |y|≤epsilon. Updating additive information from those rows with prior mean0 gives mean0, so its sharp infinity-norm error radius is2epsilon. At epsilon=.01 this is.02, achieved at(−.02,.01). This is a mathematical synthetic localization model, not a calibrated camera experiment.

At epsilon=1/4, world(.75,−.25) fits another branch and violates the claimed2epsilon x-bound. Thus strict rejection at the boundary matters. With only three rows, three distinct branches remain; choosing one fitted explanation loses admissible worlds. With all four rows but an unjustified huge precision on row1, the additive-information candidate is(17500/17503,−7500/17503). At admissible world(−.02,.01), its error is892503/875150>1: even the prior coordinate bound fails despite correct inverse algebra. Root/critic exact arithmetic and separate Lean statements reproduce the geometry and failure.

Additional exact controls distinguish assumptions:

- Adaptive biased observations z_n=mu_previous+1 all pass normalized innovation squared<1. At update3, mean13/12 exceeds the original radius1 while reported variance is1/4. These are arbitrary outliers, not a valid-noise counterexample.
- Reusing the same zero-mean measurement noise gives reported variance1/(N+1), but actual variance(1+N²)/(N+1)². The difference already appears at N=2. Noise is correlated across uses.
- Independent symmetric Bernoulli prior error and noise each have variance1. The ordinary half-gain posterior variance is1/2 before gating. Accepting innovation0 retains posterior errors±1, so conditional variance is1. The Lean statements check finite-moment arithmetic; the finite probability-law interpretation is explicitly enumerated in independent Fraction checks, not a measure-theoretic Lean development. This does not assert the same failure for the joint-Gaussian case.
- A wrong actual fault budget can leave a nonempty set around a false world. Nonemptiness cannot certify that the assumed budget holds.

## Independent critique and prototype failure

Fifteen domain gate/selection/geometric/survivor declarations and six independent critic declarations compile with permitted axioms. The critic also proves a complete4-by-4 branch theorem for two worlds sharing the same four observations: coordinate differences are bounded by6epsilon and4epsilon, with a sharp6epsilon infinity-norm example. This general branch bound is separate from the sharper2epsilon bound for the declared observation fixture. Exact polygon reconstruction independently checks all branch vertices, candidate means and inverse identities. New proof counts and hashes are recorded in pm_new_replay.json and the critic audit; failed import/tactic and axiom-parser attempts are retained and not promoted.

The Farkas prototype contains valid arithmetic certificates for the three impossible branches. Root adversarially relabeled a certificate for branch123 as feasible branch234. Its arithmetic-only evaluator accepts because it has no branch parameter and consults global inequalities. Point(0,0) witnesses that234 is feasible. The prototype also uses static manifest/duplicate assertions rather than a complete consumer. Inventor withdrew adapter acceptance and preserved the failed artifact; see pm_binding_negative.json. The mathematical bound is unaffected. No claim that a hardened checker exists is made.

## Decision and next test

**GO**, after all60 initial reviews, for one30-minute isolated consumer binding every inequality to its claimed branch, original observation ID, model/noise assumptions, complete branch manifest and returned information mean. Generate exact rational Farkas certificates for excluded branches and support bounds for retained branches. Predeclare at least20 mutations: borrowed inequality, omitted branch, negative multiplier, zero contradiction at the threshold, duplicate origin, stale model/noise bound, wrong candidate and unproved empty set. Require one accepted full artifact and independent rejection of each relevant mutation. No solver status alone counts; kernel-check promoted certificates. Extend beyond this fixture only after acceptance.

Truth containment still depends on justified prior, inlier noise and actual outlier budget. Nonlinear vision, calibration error, dynamic process propagation, scalability and physical validation remain open. The current linear test and established set-membership/coding connections are not novelty claims. Primary sources and interpretation limits are recorded in pm_sources.md (Bertsekas–Rhodes1971, Fawzi–Tabuada–Diggavi, Yang–Carlone2020).

Review quality: faithfulness4, reproducibility4, discrimination4, independent critique4, actionability3 = **95/100**. This grades the review, not readiness of the failed prototype. Subjective confidence is high in the scoped exact and formal claims; practical camera applicability remains unestablished. Root PM and three reused workers used the inherited working model, exact runtime ID unavailable; no model diversity or Spark inference is claimed.
