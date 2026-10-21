# V12: Planar camera calibration identifiability

**GO — quality95/100 (4/4/4/4/3).** AI-written four-role review, inherited root model; exact runtime identity unavailable. Subjective confidence high for stated exact mathematics, uncalibrated for real-image transfer or novelty.

## Original question and provenance

Which planar checkerboard views provide enough independent constraints to recover camera intrinsics, and how can a calibration carry a rank/consistency check?

Frozen source `/Users/mike/Dev/ctrl-research-notebook/docs/proposals/01_planar_homography.md` only catalogues Zhang calibration as an application. Its homography proof does not prove intrinsic recovery. The original source hash remains unchanged. Primary [Zhang report](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr98-71.pdf), sections3.1–4, was checked: generic five-intrinsic recovery needs three views; two require an extra prior such as zero skew. No novelty claim.

## Evidence that changes the next step

Exact fronto/two-tilt/three-view fixtures have rank2/4/5. The positive three-view fixture has nonzero skew and includes independently consumed invertible row-operation certificates, exact camera-metric binding and a kernel positive-definiteness certificate. Two tilted views admit distinct positive-definite metrics. A false zero-skew prior also yields a consistent, positive, unique answer; mathematical consistency cannot establish prior truth.

**Rank5 does not provide a noise guarantee.** Two actual common pinhole calibrations with focal lengths1000 and2999997000/999991 (more than3000), principal point(320,240), proper rational rotations and positive board depths produce27 grid correspondences differing by at most.003202529488pixels percoordinate. Shared midpoint observations fit both within.001601264745pixels. Both designs have exactrank5. Independent code reconstructs every projection and rank; kernel helpers check all54 scalar differences, rational angles, depths and the midpoint bound. This is a bounded-noise ambiguity, not an ambiguity in exact noiseless rank5 recovery or a statistical confidence claim.

A generic whole-board extension derives .0033pixels percoordinate over[-1,1]² using projective denominator/numerator bounds and exact parameters. All26 declarations, including six whole-board helpers, independently compile with permitted axioms; hashes and exits are in critic_acceptance.json. The camera-coordinate mapping is explicitly hand-checked. The finite27-point result already supports the decision.

## Three crossover routes and tests

1. Persistent excitation and experiment design: exact new constraint directions matter. Generic I/Rx/Ry metric uniqueness survives every nonzero tilt, while the weak direction scales as sin²tilt. Tiny tilts therefore retain rank but lose useful robustness.
2. Proof-carrying calibration: require rank, SPD metric, reconstruction, fixed board geometry and positive depth. Independent rank5 nullspace diag(1,1,-1) has no physical metric; a different SPD case straddles the camera plane. Radial distortion and false priors are separate model failures.
3. Gauge-aware geometric coverage and metrology: H rescaling changes raw Gram by λ⁴ without changing pixels. Per-view row-space projector is invariant under nine scale changes and three row-generator mixes in a declared coordinate metric. It is not Fisher information. Wrong board aspect ratio produces an explicit single-view alias; no generic tilted alias is asserted.

A positive quantitative fixture gives |B13|,|B23|≤2ε and |B33−1|≤41ε/8 from five normalized residual bounds, with B11=1 and3-4-5 tilts. Kernel scalar margins plus hand diagonal dominance yield SPD margin≥727/800 forε≤.01. **This epsilon is algebraic-row error, not pixel noise.** The missing pixel→homography→row perturbation bridge determines the next experiment.

## Independent critique and evidence boundary

Independent consumers reconstruct literal rows, U·A=RREF and two-sided row-operator inverse, all physical near-view projections and ranks, SPD/indefinite and depth negatives, and projector identities. Mutated records are rejected. Failed Lean attempts with sorryAx are preserved and excluded; successful replays use only propext, Classical.choice and Quot.sound. Counts/hashes are in critic_acceptance.json. Exact algebra, finite physical-model projections, generic kernel lemmas and hand camera-composition arguments remain distinct. No general noisy calibration algorithm, lens-distortion theorem, physical validation or novelty claim.

## PM decision and next action

GO for one30minute block after all60 breadth reviews: a consumer-owned camera/board/coordinate/prior/noise manifest, exactrank/SPD/cheirality certificates, and one quantitative noisy-image gate. Predeclare20 semantic controls in next_block_protocol.json. Either bound image-to-row perturbations or directly certify candidate-camera reprojection against pixel intervals; do not relabel row residuals as pixel uncertainty. Unsupported models return unknown.

Detailed evidence: domain.md, inventor.md, critic.md, pm.md and their attributed scripts/Lean logs. Actual substantive timestamps in state.json; preparation excluded. Required repository checks and account-shared resource snapshots under resources/. No publicCLI or hardware integration.
