# V05 — Robust point-cloud registration

**PM gate: GO for complete ambiguity sets and a geometry-aware next-measurement test.** A selected optimum alone is insufficient for an unqualified pose label. Quality19/20 (95%); no novelty or physical-validation claim.

Original question: Which translation/rotation/scale ambiguities and outlier patterns prevent a certifiable rigid point-cloud registration on small fixtures?

Provenance: /Users/mike/Dev/ctrl/.agents/teamwork/explorer_survey_vision_1/handoff.md, frozen/current hash in source_binding.json. This source only catalogued TEASER; it was not evidence of a prior algorithm audit. The original question and sources remain unchanged. Root PM, domain inventory_math, inventor inventory_vision_robotics and critic inventory_controls_safety used the inherited root model; exact model identifier unavailable. AI-written research, with independent role checks rather than claimed model-family diversity.

## Three transfers

1. **Error-correcting support distance.** With fixed correspondences and at most f faulty pairs, two admissible fits share at least n−2f pairs. Three shared noncollinear exact sources identify the same proper rigid transform. Count alone fails for collinear overlap; positive noise requires a quantitative geometry margin. This transfers fault-isolation logic to identifying which pose claims the data actually support.
2. **Compatibility graphs plus orientation and model binding.** Pairwise distance exclusions give a lower bound on the number of saturated TLS residuals. A clique is only necessary consistency: a reflected tetrahedron has all pair distances correct yet no proper rigid fit of all four points. Preserve labels, scale, noise threshold, determinant and actual residual objective; test each independently.
3. **Unexpected experimental-design transfer.** Choose a new feature to maximize the smallest predicted separation across every surviving pose pair. A discarded alternative can change the best query. Preserve a complete candidate set and measurement-error model; physical feature availability and visibility are additional inputs, not guaranteed by the optimization.

## Exact continuous-objective fixture

Six distinct source points form two unit right triangles at z=0 and z=1. Targets leave the lower triangle unchanged and translate the upper triangle by10 along x. Correspondences are fixed. Objective is sum min(squared Euclidean residual,1).

Every cross-group source distance is≤7/4 and target distance≥9. For any Euclidean isometry, residuals below1 cannot occur in both groups; at least three terms saturate. Identity and translation(10,0,0) each attain cost3. The continuous global lower bound and both distinct witnesses are kernel checked, not inferred from a finite candidate search.

The bound also survives unknown positive scale: for scale≤4 the cross-group incompatibility remains; for scale>4 within-group distances imply cost≥4. The kernel theorem covers any nonnegative distance-scaling map. Thus these two proper rigid poses remain global minima in the larger similarity model. Exactly-two classification for SO(3), and four if reflections are allowed, is separately hand-derived using equality and three-point uniqueness; it is not a fully assembled kernel classification.

A seventh genuine pair(0,0,2)→(0,0,2) extends the same exact graph checks to groups4+3. Cost3 then forces four exact affine-basis matches; identity is the unique optimum even allowing reflections. The four-anchor isometry identification lemma is kernel checked; its composition with the seven-point TLS equality argument remains hand-derived. Repeating a row is not an independent measurement, and objective uniqueness does not establish acquisition truth.

Threshold mutation: at epsilon7.5, translation(5,0,0) has normalized TLS8/3, below the old two poses' cost3. Reusing the epsilon1 certificate would be wrong. Exact fixtures and independent consumer are pm_fixture.json and critic_pm.json.

## Complete alternatives and a useful active query

A separate four-pair reflected-tetrahedron fixture with one allowed fault has FOUR proper three-inlier fits, not the initially expected two. Independent rational triple enumeration reproduces all four. Every qualifying support contains a noncollinear triple, giving completeness for this exact, fixed-correspondence model.

Adding a fifth pair at(0,2,1), with matching target, leaves one four-inlier proper fit. Choosing(2,0,0) leaves two because the shared support is collinear. If O(3) is silently allowed, the original reflection supplies another explanation. A regular tetrahedron has one full-support pose with fixed labels but12 proper poses when correspondence permutations are searched. These are different problems and retained negative controls.

Among57 integer virtual query points with squared norm≤5,(-1,-1,-1) uniquely maximizes the minimum prediction separation over all six pairs of the four candidate poses. Its minimum squared separation is8; the initial(0,2,1) query scores4. Root's concrete prediction-distance and radius-one disjointness lemmas are kernel checked, while their pose binding, complete enumeration and finite maximization are exact Python/analytic evidence.

Sharp scoped positive: retain the old four exact pairs, allow one total outlier, and allow error≤1 only on the new query. Any four-support candidate must match an old noncollinear triple, hence belongs to the enumerated four. At the selected query, radius-one prediction balls are disjoint. At the initial query, readout(0,2,0) fits two candidates within1. This does not certify a continuous noisy-prior family. Three nearly collinear noisy source points already permit a180-degree rotation ambiguity despite nonzero triangle area.

## Critique and acceptance boundary

TEASER's primary paper already discusses copied-scene and symmetry ambiguity and gives conditional recovery statements. Its rotation certificates and specific rank-one uniqueness conditions must not be misrepresented as certifying our entire joint registration objective. We did not run TEASER or discover an algorithm defect. See pm_sources.md.

Root freshly replayed19 printed declarations across four modules, with only propext, Classical.choice and Quot.sound. Original Mathlib build artifacts were reused; campaign domain_fixture was rebuilt before its dependent scale module. Successful logs and hashes are in pm_kernel_acceptance.json; failed prototypes are retained.

Promoted evidence comprises independently checked exact fixtures, continuous lower-bound kernel lemmas, and a finite complete-candidate discrimination test. Required distinctions remain: known labels versus matching search; SO(3) versus O(3); fixed versus free scale; max consensus versus TLS; optimum versus uniqueness versus physical truth. No actual camera, robot, point-cloud acquisition or feasible feature-pool validation occurred.

Quality rubric: faithfulness4, reproducibility4, discriminatory value4, independent critique4, actionability3=95%. Subjective confidence is high in scoped exact fixtures and finite selection; physical utility and novelty are unestablished. Quality is not probability of success.

## Next action

After all60 initial reviews, one30-minute ambiguity-aware query block with20 predeclared semantic mutations. Bind candidate coverage, correspondence/fault/noise models, orientation and scale to the consumer. First retain exact old pairs and test noisy new readings plus a declared feasible-query mask; extend to noisy prior pairs only with complete pose enclosures. Return the remaining set or abstain when evidence does not distinguish it. Independently reject omitted candidate branches and threshold/model relabeling before promoting a pose-selection claim.
