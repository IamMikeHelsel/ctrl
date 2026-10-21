# V05 domain review: certificate of optimality versus identification

AI-assisted domain researcher; inherited root model, exact identifier unavailable. Root owns timing and PM decision. Original sources remain unchanged.

## Original question and inspected depth

Which translation, rotation, scale and outlier ambiguities prevent certifiable rigid point-cloud registration on small fixtures? The frozen provenance is a catalogue entry for TEASER in `.agents/teamwork/explorer_survey_vision_1/handoff.md`, copied into `source_snapshot_0.txt`; that entry is not an algorithm audit. This review inspected the primary paper's formulation and estimation-contract discussion, and constructed an independent exact fixture. No TEASER implementation was executed or audited.

The [primary TEASER paper](https://arxiv.org/html/2001.07715v2) distinguishes posterior optimality certificates from estimation contracts. Its §IX.A explicitly describes adversarial transformed copies as an identifiability obstruction; Theorem16 imposes additional inlier-count, noncollinearity and algorithm-output conditions for exact recovery. Its rotation certificate applies to a particular decoupled subproblem. Therefore our construction is a small regression/certificate-scope test of a known limitation, not a novel impossibility theorem or a refutation of TEASER's guarantees.

## Exact observation model

There are six fixed labelled correspondences. Known-scale baseline is Euclidean rigid registration, scale1, R in SO(3), arbitrary translation t. The objective is full-vector TLS with unit threshold: sum over six pairs of min(||R x+t-y||²,1). This is not componentwise translation TLS and not the exact decoupled TEASER rotation objective.

Group A sources and targets are (0,0,0),(1,0,0),(0,1,0). Group B sources are (0,0,1),(1,0,1),(0,1,1), with targets obtained by adding (10,0,0). All six source points are distinct, source coordinates lie in[0,1], and each group is noncollinear. Correspondence search and permutations are excluded.

Two possible truth assignments give identical observed pairs: either groupA is noiseless truth and groupB is adversarial, or the reverse. Both have exactly three inliers and three outliers. No estimator using only those observations can determine which truth assignment occurred.

## Discriminating continuous certificate

For every cross-group pair, source distance is at most sqrt(3), hence at most7/4; target distance is at least9. A distance-preserving map cannot place both residuals below1: the triangle inequality would demand target separation at most source separation plus the two residuals.

If some groupA residual is below1, all three groupB residuals saturate TLS, giving cost at least3. If no groupA residual is below1, groupA itself contributes3. Thus every Euclidean isometry has cost at least3. The identity pose and the translation by(10,0,0) each attain exactly3; each has identity rotation with determinant+1. The poses differ by10 in translation.

The lower bound is proved over the larger class of all isometries, so it also excludes a cheaper reflection in O(3). The two attaining witnesses are in the desired proper-rigid SO(3) class. A larger admissible class in the lower-bound proof does not weaken their proper-pose validity. The theorem does not yet classify every minimizer or establish uniqueness after adding a trusted datum.

## Transfers and falsifiers

1. Fault isolation: represent each hypothesized inlier subset as an admissible explanation, retaining both explanations rather than forcing a single label. The preserved object is the common observation array; an independent trusted correspondence or authority assumption can falsify an explanation.
2. Graph consistency: cross-group distance conflicts make the compatibility graph two disjoint triangles at the unit residual threshold. Its maximum clique is not unique. A clique certificate certifies a combinatorial optimum, not the truth label or a unique pose.
3. Optimization duality: a global cost lower bound together with two attaining poses provides an ambiguity certificate. The failure test is whether a downstream acceptance rule incorrectly turns either optimality certificate into a unique physical estimate.

These are local structural transfers. The existing paper already uses graph consistency; no novelty is claimed for that idea.

## Scale boundary

The baseline proof assumes distance preservation. The separately compiled `domain_scale.lean` proves TLS≥3 for every map satisfying dist(Tx,Ty)=s·dist(x,y), with s≥0. For s≤4, scaled cross-group separation is at most7 while target separation is at least9. For s>4, each group's distinct source points are at least1 apart but targets within that group are at most2 apart, preventing two subunit residuals in a group. The Lean proof obtains the stronger cost≥4 in this second case. Therefore the two scale1 proper-rigid witnesses remain global minima in the larger positive-scale similarity class. No bounded-scale assumption is required for this particular fixture.

Hand-derived equality classification, not yet a kernel theorem: when s≤4 and cost3, either one A residual is subunit and all B terms saturate, forcing every A residual to zero, or all A terms saturate and every B residual is zero. Three labelled noncollinear exact pairs determine a positive-scale SO(3) pose, yielding only the two displayed proper poses. O(3) additionally admits the corresponding reflection about each inlier plane; these are not extra proper rotations. The kernel package certifies lower bounds and two distinct witnesses, without asserting this full classification.

## Artifacts and checks

`domain_fixture.py` / `.json`: arbitrary-precision rational squared-distance checks for all9 cross-group pairs, distinct source/target coordinates, noncollinearity, and both exact attaining residual arrays. Both arrays are three zeros and three100s, in opposite orders. This script does not optimize over rotations; the continuous lower bound is in Lean.

`domain_fixture.lean`: eight printed declarations, producer-compiled using ctrl's pinned Lean4.33.1. They prove cross-source and cross-target bounds, residual incompatibility, continuous TLS lower bound, identity attainment, translation attainment, translation isometry, and pose distinctness. Standard axioms only. Independent replay requested on frozen bytes. `domain_scale.lean` adds seven printed declarations for the general scaling lower bound and its supporting distance/cardinality inequalities; all producer closures have only permitted axioms. Failed preliminary vector-conversion/elaboration logs and a name-discovery API scratch probe are retained; no failed draft is accepted.

Run from repository root: `uv run python work/pod/crossover-60-20261018/cards/V05/domain_fixture.py`. Ruff check and format applied to that isolated script. Lean compile from `lean/`: `lake env lean ../work/pod/crossover-60-20261018/cards/V05/domain_fixture.lean`. This uses existing Mathlib dependencies; it is not a fresh full repository build or hardware validation.

## Domain decision recommendation

GO for ambiguity-aware certificate acceptance and a next small trusted-data test. NO-GO for treating global TLS optimality alone as uniqueness or truth under arbitrary adversarial outliers. Next action: add one explicitly trusted correspondence and certify whether it eliminates one of these two explanations, without silently extending that result to all other possible poses.

Quality18/20=90% (A−): faithfulness4, reproducibility4, discriminatory value4, critique3, actionability3. Subjective confidence97% in the baseline mathematical scope after independent replay; no claim of new research novelty, implementation correctness or physical registration acceptance.
