# V05 inventor: geometry-aware support distance and informative point choice

AI-written by an independent role using the inherited root model; exact runtime model identifier unavailable. Original survey is a catalogue, not an audited implementation. PM owns elapsed-time accounting and the decision. No original source, solver, robot, or registration implementation was changed.

## Source boundary

Frozen question: which translation/rotation/scale ambiguities and outlier patterns prevent a certifiable small rigid point-cloud registration? Read campaign CHARTER, root AGENTS, CARD, and source_snapshot_0. Primary source checked: [Yang, Shi, Carlone, TEASER](https://arxiv.org/abs/2001.07715), abstract and bibliographic entry. It describes TLS with outlier correspondences, graph pruning, and conditional optimization certification. Its empirical high-outlier performance is not a universal identifiability theorem. Full paper and software were not audited. MIT repository page retry returned HTTP429; no claim depends on that retry. These experiments are original small deductions, with no novelty claim.

## Transfer 1 — error-correcting codes with geometric support distance

Map a proper rigid transform T to its prediction word `(T(p_i))_i`. A corrupt correspondence is an arbitrary symbol error. Distinct transforms must have sufficiently separated prediction words for unique fault correction. The symbols here are points, not finite alphabet labels; Hamming distance concerns exact equality only.

For fixed labeled pairs, known scale1, zero inlier noise, and at most f faulty pairs, two admissible transforms have supports of size at least n−f. Their intersection has at least n−2f indices. If those shared sources contain three noncollinear points, the transforms coincide: the relative proper rotation fixes two independent displacement vectors and their cross product, hence fixes a basis; translation then agrees. Therefore the sufficient condition is **every subset of n−2f source points contains a noncollinear triple**, not merely a count. If no three sources are collinear, n≥2f+3 suffices. Equivalently, distinct rigid prediction words differ in at least n−2 coordinates and can correct f errors when 2f<n−2.

Test: sources `(0,e1,e2,e3)` and targets `(0,e1,e2,−e3)`, f=1. Initially predicted exactly two candidate transforms; exhaustive rational triple enumeration falsified this: there are FOUR proper three-inlier fits, one for each triangle. Identity and x-axis half-turn are only two of them. The fourth has rational thirds and nonzero translation, recorded in JSON. This failed preliminary assertion is retained in this note and the script comment; it was not solver evidence.

Falsifier for raw count: add fifth pair p=y=(2,0,0), keeping f=1. There remain TWO four-inlier proper fits, sharing the three collinear x-axis points. Thus n=5,f=1 alone does not give uniqueness.

Boundaries: the same noiseless overlap proof extends to positive uniform unknown scale, provided two shared points are distinct: their nonzero distance first forces equal scales, after which the proper-rigid argument applies. It does not cover arbitrary affine maps, nonuniform scale, signed scale, or correspondence search. No free-scale solver was tested here. With positive noise, exact equality and the code-distance argument must be replaced by separation and conditioning bounds.

## Transfer 2 — graph consistency plus an orientation witness

Pair-distance constraints are parity-like local consistency checks: every proper rigid fit preserves each pair distance. They are useful necessary conditions and can prune incompatible correspondence sets. The missing invariant is chirality. A global reflected tetrahedron preserves all six distances and yields a complete pairwise consistency graph, yet its full affine map has determinant−1. Three points are always planar and cannot witness this distinction; a signed nonzero tetrahedral volume can.

Our first four pairs are exactly such a reflection. After adding p=y=(0,2,1), the f=1 SO(3) problem has a unique four-inlier fit (identity). If O(3) is allowed, reflection diag(1,1,−1) still fits all original four pairs, so the apparent uniqueness disappears. The script checks its determinant and support directly. Critic independently proposed and checked the same chirality failure with an equivalent coordinate reflection.

Preserved invariant: distances and orientation sign under proper rotations. Breaks: signed volume is zero for coplanar points; noise requires a nonzero orientation margin rather than a raw sign test; passing all graph edges does not certify SO(3) feasibility, support truth, or optimization uniqueness. An orientation witness must be bound to the actual correspondence indices and coordinates.

Additional correspondence-search negative: regular tetrahedron vertices `(1,1,1),(1,−1,−1),(−1,1,−1),(−1,−1,1)` have ONE proper full-support fit with identity labels, but TWELVE when all24 label permutations are searched. Known matches and unlabeled cloud registration are distinct problems even with no outliers.

## Transfer 3 — unexpected: choose a new feature as a separating experiment

Instead of asking the optimizer to resolve an unidentifiable dataset, treat the remaining transforms as competing hypotheses and select a prospective correspondence whose predicted locations differ. This transfers active experiment design to finite registration ambiguity. A query on a shared rotation axis supplies no distinguishing evidence; an off-axis query can. No physical acquisition mechanism or feasible robot motion is asserted.

Exact test: adding fifth pair p=y=(0,2,1), with the same absolute f=1 budget, leaves only identity with four inliers. All ten source triples are noncollinear, providing a geometry-based uniqueness argument independently of the enumerator. The fifth point is not silently declared trusted; the total fault budget remains1. Each former hypothesis already uses its allowance on one of the original four pairs, so an inconsistent fifth pair cannot also be discarded.

Play extension: among57 integer candidate points with squared norm≤5 and coordinates in[−2,2], maximize the minimum squared prediction separation across ALL FOUR original hypotheses. The initially chosen `(0,2,1)` scores4; the unique maximizer `(−1,−1,−1)` scores8. This is an exhaustive finite virtual candidate pool, not an optimum over continuous acquisition choices.

Discriminating noisy-query extension, declared separately: original four pairs remain exact; only the added measurement has Euclidean error≤1. At `(0,2,1)`, observation `(0,2,0)` is admitted by identity and the y-axis half-turn, so both remain viable. At the maximizer, every pair of predicted points has squared separation≥8>4, and no radius-one observation can fit two of the finite hypotheses. This uses truth coverage and the unchanged fault budget. It does not handle positive noise on the original four pairs, which would produce continuous candidate sets.

## Noise and conditioning negative control

For any epsilon>0, sources `(0,0,0),(1,0,0),(2,epsilon,0)` are noncollinear. Targets `(0,0,0),(1,0,0),(2,0,0)` admit both identity and the x-axis half-turn with zero outliers and residual norms `(0,0,epsilon)`. At epsilon=1/100 the exact squared triangle area is1/40000, while the two rotations' squared Frobenius separation is8. Thus noncollinearity without a quantitative margin gives no small rotation-error guarantee. Even for a fixed pair of hypotheses, prediction separation exactly2epsilon is insufficient: their midpoint lies in both closed error balls. Strict separation is required for worst-case single-query discrimination.

## Evidence, critique, and next action

`inventor_support.py` uses Fraction throughout, constructs the unique proper map from each congruent noncollinear labeled triangle, verifies its orthogonality and determinant1, and counts exact supports. For these fixtures every qualifying support contains a noncollinear triple, so enumeration is complete. Output includes the actual transformations and counterexamples. Support fixtures retain fixed labels; the separate regular-tetrahedron experiment explicitly enumerates all24 permutations. This is exact executable evidence and a mathematical derivation, not a Lean kernel certificate or physical validation. No TLS optimality result is claimed from maximum support alone; PM/domain own their separate TLS fixture.

Independent replay was requested from the critic; status is recorded by their note. The script passes scoped Ruff checks and formatting. Repository-wide checks and any integration are PM-owned; no integrated source change was made.

Recommendation: GO for a bounded ambiguity-aware acceptance adapter. Inputs must bind correspondence identities, geometry, SO(3)/O(3), fixed/free positive scale, noise bounds, and total fault budget. Return the complete admissible hypothesis set or a justified enclosure; separate objective optimality, identifiability, and conditional estimation error. Next test: a complete noisy branch enumerator with rational separation witnesses, plus mutations that remove a branch, change one correspondence label, switch orientation group, or increase f. HOLD a physical active-acquisition claim until a realizable feature pool and measurement model are supplied.

Quality rubric: faithfulness4, reproducibility4, discrimination4, critique4, actionability3 =19/20 (95%). Subjective confidence is high in the exact fixtures and conditional support argument; this is not a probability of novelty or operational success.
