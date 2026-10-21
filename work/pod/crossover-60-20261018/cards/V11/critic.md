# V11 independent critique

AI-written independent review, inherited root model with exact model identifier unavailable. Original files and approved challenges preserved. Exact arithmetic, conditional kernel proofs, statistical examples and physical-model acceptance remain distinct.

## Original source scope

InformationFilter.lean proves Woodbury and covariance/information inverse identities in an arbitrary associative Ring. Its hypotheses contain no true state, estimator mean, inlier event, probability law, unbiasedness, independence, positive definiteness or geometric rejection rule. Those algebraic identities are useful but do not imply an actual estimation-error guarantee. The prose description of an optimal minimum-variance update needs statistical hypotheses outside these formal statements. A square-ring specialization also does not by itself formalize a general rectangular observation operator.

An exact control takes P=R=U=1,V=−2: the inverse identity holds with posterior quantity−1. This is not a valid covariance model (in particular U and V are not a transpose pair); it demonstrates that the ring theorem itself is not a positivity/error theorem. No source algebra bug is alleged.

## Independently verified failures

critic_exact.py uses Fraction arithmetic without producer imports:

- Precise biased observation: truth/prior mean0, P1,R10⁻⁶,z.1 passes a three-sigma innovation gate. The new mean is100000/1000001 while reported variance is1/1000001; squared actual error exceeds9 times that variance. The measurement is deliberately biased, so this refutes misuse of the algebra/gate, not a correctly specified noise model.
- Repeated correlated observation: X and B are independent equiprobable±1, prior mean0, and every copy observes the SAME z=X+B. Each measurement noise is unbiased with variance1, but copies are perfectly correlated. Naive reported variance is1/(N+1); actual error variance is(1+N²)/(N+1)². AtN2 these are1/3 and5/9; atN100,1/101 and10001/10201. All four outcome histories pass three-sigma innovation gates.
- Sequential poisoning independently reproduces root's construction z_n=mean_(n−1)+1: P_n=1/(n+1), mean_n=sum_(k=2)^(n+1)1/k, normalized innovation squared n/(n+1)<1. AtN3 the error13/12 exceeds the original deterministic radius1. This intentionally violates trustworthy bounded measurement noise.
- Innovation/interval compatibility certifies only that SOME truth could fit both sets. The domain witness truex−1, prior0±1,z21/20±.1 satisfies compatibility but not actual measurement validity; posterior error206/101 exceeds1.
- Repeating the same valid bounded-error interval leaves the feasible set unchanged. Reuse is not independent information.

critic_selection.py independently enumerates four product-law Rademacher worlds. Residual-zero admission preserves only equal-sign errors, raising conditional posterior variance from1/2 to1 and cross moment from0 to1. This is an explicit non-Gaussian finite-law example, not a claim that correctly specified jointly Gaussian innovation conditioning has the same failure.

## Positive deterministic repair and its assumptions

The actual truth must belong to the prior and admitted observation feasible set. For a nonempty scalar interval[L,U], a proposed estimate c has error at mostE for every feasible truth exactly when c−E≤L and U≤c+E. Information weights may still generate c, but their inverse matrix is not the deterministic radius. The valid fixture x3/5,z1/2,b.1 produces c50/101 and sharp interval radius53/505; its squared actual error can exceed reported covariance1/101 despite both hard bounds being valid.

The domain's eight gate lemmas independently compile using only permitted axioms. They include endpoint sufficiency/necessity, actual-truth interval membership, information/gain mean equality and the sharp prior-only obstruction: preserving radius a for every truth in prior mu±a permits no nonzero displacement without further trustworthy information. A nonempty intersection alone does not supply that information. Empty feasible sets must lead to an explicit failure/abstention, never vacuous acceptance.

## Independent geometric reconstruction

The declared linear localization fixture has rows H=(x,y,x+y,x+2y), observations(1,0,0,0), bounded inlier error epsilon.01, prior[-1,1]² and at most one faulty original observation. These are NEW explicit model assumptions; no full nonlinear camera theorem is claimed.

critic_geometry.py reconstructs each branch from its inequalities, enumerating rational line intersections independently of producer vertices, and checks the information matrices, inverses, information vectors and means. Three rows give three feasible branches with12 vertices. Four rows give only the branch retaining rows2,3,4, with6 vertices. The good-data information mean0 has exact infinity-norm worst error1/50. The all-data high-precision bad-row candidate has worst error892503/875150>1 at the genuinely feasible world(−.02,.01). Being inside the original prior box does not preserve its former radius about a shifted estimate.

Independent analytic certificates avoid dependence on vertex enumeration: retaining row1 forces x≥1−epsilon. The alternative inlier triples123,124,134 imply x≤2epsilon,3epsilon,3epsilon respectively; for epsilon<1/4 all are impossible. The remaining234 inequalities give |x|≤2epsilon,|y|≤epsilon, attained by(2epsilon,−epsilon). At epsilon1/4, the alternate branch world(.75,−.25) survives and violates |x|≤2epsilon. Thus strict threshold and branch coverage matter.

Three critic_branch.lean statements independently compile the fixed-.01 branch exclusion, sharp bound and exact bad-candidate witness. Two critic_geometry.lean statements compile the six possible common-row pair bounds and a sharp pair. The general four-row two-world diameter bound is6epsilon in infinity norm: any two one-outlier worlds share at least two inlier rows; those imply |delta_x|≤6epsilon,|delta_y|≤4epsilon. Worlds(0,0) and(6epsilon,−4epsilon) with observations(0,−4epsilon,epsilon,−epsilon) attain6epsilon and each have only one faulty row. The standalone pair-bound theorem takes the six-way shared-pair condition explicitly. The additional critic_fault_bridge.lean independently compiles the full 16 combinations of complete three-of-four branch assumptions for two worlds sharing the same observation vector, proving both coordinate bounds directly. Thus that bridge is also kernel checked; the real-world validity of the declared fault budget remains an external premise.

Truth coverage requires the stated fault budget for original observations. Duplicating or relabeling a faulty observation cannot create independent geometric redundancy. A uniqueness/empty-branch calculation cannot certify that its own fault-budget premise holds. Repeated information updates require provenance or a justified joint noise model; hard-set reuse remains idempotent.

## Final independent replay and consumer boundary

Independent recompilation also passed all three domain_selection.lean arithmetic declarations, all three domain_geometry.lean general-epsilon declarations, and domain_survivor.lean's certified_survivors. The last theorem returns actual bounds for admitted rows 2, 3 and 4 from complete branch coverage and the strict threshold, providing a meaningful premise for a fusion consumer. All printed declarations use only propext, Classical.choice and Quot.sound. The finite probability-law interpretation and physical measurement assumptions remain explicit external bindings.

critic_farkas.json independently reproduces a semantic gap in the prototype certificate evaluator by invoking its actual function: a valid contradiction using rows 1, 2 and 3 returns True when presented as a rejection of branch 2, 3 and 4, even though that branch contains (0,0). The arithmetic sum is correctly (0,0,−97/100); the consumer has no claimed-branch/model argument with which to reject the mislabeled certificate. Existing set/length assertions exercise static fixtures rather than enforcing complete coverage and unique provenance at the acceptance entry point. This does not refute the branch theorems. It prevents promoting the prototype as a hardened runtime certificate checker.

A next block should bind every certificate row to the claimed branch and model, require complete branch coverage and original-observation provenance, and bind the proposed mean to the same admitted measurements. Replay wrong-branch, missing-branch, duplicated-origin and altered-mean mutations through the actual consumer API.

## Decision

GO for an estimator with additive information proposals plus a separate nonempty, truth-covering geometric feasible-set certificate and explicit worst-error gate. NO-GO for covariance decrease or an innovation threshold alone as an actual-error guarantee. HOLD the runtime certificate adapter until branch/model/provenance binding is enforced, and HOLD claims about real camera measurements until their observation relation, hard error budget, fault provenance and prior coverage are supplied. This is conditional certification, not a universal robust filtering discovery.

Subjective quality19/20 (source4, independent checks4, negatives4, calibration4, closure3). This score is not a probability. No physical or full-repository acceptance claimed. Initial critic path error for a standalone Lean file is preserved; successful corrected proofs alone are accepted. Scoped Python checks pass after formatting.
