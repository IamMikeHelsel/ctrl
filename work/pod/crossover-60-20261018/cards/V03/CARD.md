# V03: Epipolar validity versus pose identifiability

**PM: GO for a bounded pose-certificate experiment after the breadth pass.**
AI-written by four roles. Quality19/20(95%): faithfulness4, reproducibility4,
discriminatory value4, independent critique4, actionability3. Subjective confidence is high
in the stated exact examples; utility on real data and novelty are unestablished.
This grade is not a probability of discovery or physical safety.

## Original question and provenance

When do calibrated two-view correspondences determine a rigid pose, and how do planar
scenes or zero baseline affect identifiability without invalidating the epipolar identity?
Frozen roster V03, investigated source rather than catalogue-only entry:

- `/Users/mike/Dev/ctrl-research-notebook/ControlsLean/Vision/Epipolar.lean`
- `/Users/mike/Dev/ctrl-research-notebook/docs/proposals/01_planar_homography.md`

The Lean source correctly proves a forward algebraic identity from the depth-scaled
motion equation, assuming only nonzero second depth. It does not prove inverse uniqueness
or proper rigid-pose admissibility. The proposal's claim that epipolar geometry is valid
only for noncoplanar scenes is false; incidence remains valid on planes. A projective
family of fundamental matrices cannot automatically be called an equally large family
of calibrated essential matrices. Original files were preserved.

## Creative transfers and assumptions

1. **Control observability:** remove translation-scale gauge before testing local rank.
   It preserves differential information but cannot count separated global solutions.
2. **Elimination and proof obligations:** keep SO(3), finite nonzero rays and strictly
   positive depths when eliminating latent structure. Polynomial incidence preserves
   a necessary condition, not every physical side condition.
3. **Active identification:** choose evidence by separation of surviving pose hypotheses.
   More points, nonplanarity or increased local rank alone may be uninformative.
4. **Unexpected coding-theory transfer:** treat hypotheses as feasible measurement sets
   and compare their uncertainty neighborhoods. These are sets with latent depths, not
   single codewords; exclusion is easier than positive physical acceptance.

All constructive camera results use real calibrated normalized pinhole bearings, an
unknown static rigid scene, exact correspondences or explicitly bounded synthetic errors,
and positive scene depths. Alternative reconstructions may change the unknown scene.
Known metric target geometry would be a different problem. No occlusion, distortion,
calibration-error or physical actuation model is supplied.

## Tests and results

**Two physical solutions.** H=[[1,0,1],[0,1,0],[0,0,1]]. PoseA has R=I,t=(1,0,0).
PoseB has R=[[3/5,0,4/5],[0,1,0],[-4/5,0,3/5]],t=(1/5,0,2/5).
For x=(u,v,1),u>−1/2, both yield y=(u+1,v,1) with positive depths. The rotations and
translation directions differ. Domain/critic use the displayed B scale; inventor uses
translation5times larger and correspondingly larger scene depths and E. This is explicit
scale conversion, not a disagreement.

**Local rank does not settle global uniqueness.** Both pose Jacobians have exact rank5
after removing the sole translation-scale mode. PM independently checked288 derivative
entries via rational Cayley rotations and translation differences. Two added critical
points yield14 distinct ray pairs and noncoplanar reconstructed scenes under both poses;
independent affine determinants are1/6 and−62500/741. Both local ranks remain5. Thus even
noncoplanarity, cheirality and full local rank together do not guarantee global uniqueness
for this deliberately critical configuration.

**Mechanism.** For A-world(X,Y,Z), the competing residual is2Y(Z−1)/Z² in inventor scale.
Its zero set is a union of two planes; full depth conditions are checked separately.
The critical compatible-matrix pencil has two essential classes, c=0 and c=2a. Three PM
Lean lemmas check the explicit cubic entry and branch sufficiency. This is a particular
family analysis, not a general decomposition or novelty claim.

**Positive identification test.** Domain's nine planar pairs plus two predeclared
separating off-plane pairs have design rank8. An independently audited Lean theorem
proves directly that their eleven incidence equations force F into the E_A matrix line.
A separate hand derivation excludes t=0 using unequal bearing angles, then uses proper
rotation and positive depths to force R=I,t=τe1,τ>0. This gives exact uniqueness up to
positive global scale for that fixture. The full combined uniqueness theorem is not yet
kernel-checked. Inventor also supplies a distinct15-pair rank8 fixture.

**Finite precision.** PM's exact multi-affine interval experiment allows1/100 error in
each finite ray coordinate and each of nine entries around inventor E_B. For the
transverse depth2 point, the residual interval is[25667/90000,34369/90000], so the entire
specified candidate box is excluded. Producer enumeration and independent integer
replay check8192 vertices percase. Nearplane and critical-direction controls retain0.
An interval containing0 is inconclusive, not a physical compatibility certificate.
Scale changes require uncertainty-radius changes. No complete alternate-pose cover or
real error-model justification is supplied.

**Conditioning.** With fixed unit translation and plane depth1/β, a5×5 local minor is
2β². Rank persists for positiveβ but the chart's squared condition number is at least
7/β². This is diminishing parallax from distant structure, not a finite zero-baseline
limit. Pure rotation has E=0 and a vacuous epipolar equation, but bearing data can still
constrain rotation. A nonzero E may fit those scalar equations yet admit no finite lift.

## Independent critique and evidence levels

The critic independently reconstructed scenes, ranks, intervals and conditioning; checked
matrix-scale conversions; compiled isolated Lean files; inspected scalar-to-ray binding;
and rejected corrupted rotations, depths, derivatives, bounds, claimed ranks, duplicated
separators and invalid cheirality. Full details and artifact names are in `critic.md`.
A first off-plane v0,depth2 example was only algebraically compatible and forced zero
candidate depth. It was rejected as a physical witness and replaced with strictly positive,
distinct-ray examples. This correction is preserved in role notes.

Kernel evidence consists of24 domain lemmas plus3 PM polynomial lemmas, with only
propext, Classical.choice and Quot.sound. Exact rational Python evidence covers rank,
conditioning and interval certificates. The global pose conclusion still uses a reviewed
mathematical bridge. No numerical solver status is promoted as proof. No physical robot
validation, new vision algorithm, exhaustive literature review or novelty claim is made.

The original source could not compile in its own notebook environment because its pinned
Mathlib build was missing. A byte-identical copy compiled under the existing ctrl4.33.1
environment, with provenance and axioms recorded. That is a compatibility replay, not a
claim that the original environment passed. Failed compile attempts and deliberately false
controls remain in logs and are excluded from accepted evidence.

## Precise next action

After all60 initial reviews, spend30minutes on an isolated layered certificate interface.
Predeclare at least20 fixtures across planar, critical nonplanar, separating nonplanar,
pure-rotation and small-parallax cases. Compare residual-plus-local-rank acceptance with
physical lifts, retained alternatives and interval exclusion. Mutate matrix scale, depth,
correspondence binding, candidate completeness and duplicate observations. A uniqueness
label requires a complete candidate cover or a checked sufficient argument; omitted
candidates must fail closed. Formalize the remaining rank-to-pose bridge before calling
that end-to-end result kernel-certified.

General noisy global uniqueness, calibration robustness and physical robot use: HOLD.
Low residual or local rank promoted directly to global uniqueness: NO-GO.
The bounded experiment above: GO. See `pm_synthesis.md` for primary sources and reasoning.
Timing and resource snapshots are in campaign state/activity/resources; preparation and
a context-transition gap were excluded. Ten minutes reviewed is not ten minutes proved.
