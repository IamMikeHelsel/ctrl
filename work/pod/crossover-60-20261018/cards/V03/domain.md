# V03 domain review — identity, model validity and pose identifiability

AI-written role work; inherited root model, exact runtime identifier unavailable.
Root PM owns timing and final decision. Source and approved Challenge files were not edited.

## Recovered statement and source-prose defect

Inspected original files:

- `/Users/mike/Dev/ctrl-research-notebook/ControlsLean/Vision/Epipolar.lean`
- `/Users/mike/Dev/ctrl-research-notebook/docs/proposals/01_planar_homography.md`

The existing epipolar theorem is an algebraic implication over any field: given
`d2*x2 = R*(d1*x1)+t` and d2 nonzero, it proves x2 dot([t]cross R x1)=0.
It does not require R to be a rotation, nonzero translation, nonzero rays, positive
depths or nonplanarity. This is a useful and valid general identity. It does NOT prove
that an arbitrary matrix called `essential` is a physically valid essential matrix,
that correspondences satisfying the scalar identity have a positive-depth reconstruction,
or that the reconstruction is unique.

The proposal says epipolar geometry is valid only for noncoplanar configurations.
That is false, and its explanation that all epipolar lines meet at epipoles describes
ordinary epipolar geometry, not a special planar failure. Planarity changes inference
from correspondences; it does not invalidate the identity. Nor does presenting a
homography automatically resolve pose ambiguity.

Other boundaries: the zero vector is not a projective image point or epipole, although
some coordinate theorems allow it. If t=0, the algebraic matrix E is zero and its scalar
constraint imposes no restriction. Rotation can still be constrained by the actual ray
mapping; no baseline means no translational parallax, not automatically no information
about rotation. An arbitrary-field statement cannot supply a positive-depth condition.
A plane-induced matrix need not be invertible merely because its plane distance is
nonzero; invertibility and valid projective images require their own hypotheses.

## Exact calibrated planar ambiguity surviving cheirality

Use normalized calibrated rays and the homography

    H = [[1,0,1],[0,1,0],[0,0,1]].

Reconstruction A has R_A=I,t_A=(1,0,0) and plane Z=1. Reconstruction B has

    R_B=[[3/5,0,4/5],[0,1,0],[-4/5,0,3/5]],
    t_B=(1/5,0,2/5), plane 2X+Z=1.

R_B is orthogonal with determinant+1, and H=R_B+t_B(2,0,1)^T.
For every ray x1=(u,v,1) with u>-1/2, both reconstructions produce x2=(u+1,v,1).
A uses depth1 in both cameras. B uses depth1/(2u+1)>0 in both cameras. Thus both
reconstructions satisfy strict cheirality on a whole image region, not merely at one
point. Their rotations differ, and their translations are not parallel; the ambiguity
is not the ordinary global positive scale gauge. The scene plane and scene points differ
between reconstructions. This is the intended unknown-scene two-view problem, not
pose estimation from a known metric calibration target.

The two actual essential matrices are

    E_A=[[0,0,0],[0,0,-1],[0,1,0]],
    E_B=[[0,-2/5,0],[2/5,0,1/5],[0,1/5,0]].

They are not proportional, and both annihilate every correspondence above. The critic
independently constructed the same rational pair before reviewing the domain script.
`domain_exact_poses.py` checks nine grid correspondences, both rigid transformations,
positive depths, the plane relation, matrix identities and nonproportionality with
Fraction arithmetic. Output is `domain_exact_poses_results.json`.

The mechanism is a rank-one alternative factorization of the same plane map. This is
an observability example: different physical states produce identical outputs, even with
perfect measurements and cheirality. More points on that same visible plane cannot
distinguish these two states. A useful next experiment must alter the observation model
or introduce genuinely independent information.

## Fundamental ambiguity is not the whole essential family

For a planar map x2 proportional to Hx1, every F=[e']cross H obeys the scalar incidence
constraint. But calibrated essentials satisfy additional constraints. In this example,
taking e'=(0,1,0) produces

    F_bad=[[0,0,1],[0,0,0],[-1,0,-1]].

It fits the exact correspondences and is singular, but fails the essential cubic
2 F F^T F - trace(F F^T) F=0. The Python script checks this failure and checks that
both actual E matrices satisfy the cubic. Thus the proposal's two-parameter projective
F ambiguity cannot simply be relabeled a two-parameter calibrated-E ambiguity. The
concrete two-pose example establishes multiple calibrated solutions without making
an unproved statement about their complete number or dimension.

## Literature checked and limits

Hartley and Zisserman's author-hosted [epipolar chapter](https://www.robots.ox.ac.uk/~vgg/hzbook/hzbook2/HZepipolar.pdf)
states that epipolar geometry is independent of scene structure; its calibrated section
characterizes essential singular values and separates recovering an essential matrix
from decomposing a given one into pose candidates. Cheirality pruning for one known E
does not establish that the correspondences selected a unique E. These points agree
with the explicit construction above.

Knight and Reid's [primary planar-degeneracy paper](https://www.robots.ox.ac.uk/ActiveVision/Papers/knight_reid_icpr2000/knight_reid_icpr2000.pdf)
describes planar correspondence maps and underdetermined fundamental geometry. It
supports the established status of this phenomenon, not novelty of our witness.
Malis/Vargas RR6303 was located through author/archival metadata, but its HAL full-text
request was access-denied and two alternative academic-host fetches failed. No claim
here depends on having reviewed that report's full contents.

## What would justify a pose claim

A physically meaningful reconstruction claim needs calibrated nonzero oriented rays,
SO(3) rotation, positive depths, an explicit nonzero-baseline assumption where required,
and treatment of global scene/translation scale. Unique pose additionally requires an
injective observation map modulo that gauge, or a checked exhaustive candidate set with
one remaining admissible element. A small epipolar residual, singular E, many points,
nonzero baseline, or cheirality alone does not establish this.

Promising follow-up: retain all admissible planar pose branches, identify an observation
that separates them, and certify how much measurement error preserves that separation.
An off-plane point, a justified plane normal/depth measurement, independent rotation
information or another view can be tested as additional assumptions. No blanket claim
that any one of those always guarantees uniqueness is made.

## Critical nonplanar observations and a separating experiment

For a point generated by A at depth Z>0 with first ray(u,v,1), the target ray is
(u+1/Z,v,1). Its E_B residual is exactly(2/5)v(1-1/Z). Therefore off-plane points with
v=0 still satisfy both epipolar equations. Residual zero alone is not a physical
reconstruction, so we also checked positive depths explicitly.

The PM's axial example x1=(0,0,1),x2=(2/3,0,1) has A depths3/2 in both cameras and
B depths1/6 and1/2. It lies off each reconstructed plane. However, that first ray
already occurs in the9-point grid. To avoid a duplicate image pixel at another depth,
use instead x1=(1/4,0,1),x2=(11/12,0,1): A depths3/2 both; B depths2/7 and18/35.
Its first and second pixels are distinct from every grid feature.

Adding the latter point makes BOTH reconstructed point clouds nonplanar: the determinants
of three displacement vectors from a retained point are1/8 for A and-1/14 for B.
`domain_nonplanar_ambiguity.lean` checks these determinants, both pose equations for
each extra observation, positive depths and off-plane conditions. Thus even nonplanarity
plus cheirality is not by itself a universal pose-identifiability condition.

A genuinely discriminating A point is X=(0,1,2), giving rays(0,1/2,1) and(1/2,1/2,1).
Its E_B residual is1/10, while its A depths are positive. `domain_offplane.lean` proves
the general residual expression, this witness and the v=0 failure line. The original
example has a repeated first-image ray if appended to the whole saved grid; the
rank-gate experiment below instead predeclares two distinct-pixel observations.

## Exact sufficient identification gate for one fixture

The predeclared rank tests in `domain_rank_gate.py` give:

| Observations | Exact design rank | Nullity |
| --- | ---: | ---: |
| Nine plane pairs |6|3|
| Plane pairs plus distinct critical nonplanar point |7|2|
| Plane pairs plus one separating point |7|2|
| Plane pairs plus two separating points |8|1|
| Plane pairs plus critical point and one separating point |8|1|

The separating pair additions use first rays(1/4,1/4,1),(1/4,3/4,1) at A depth2,
with target rays(3/4,1/4,1),(3/4,3/4,1). Every first and second pixel is distinct.
Exact rank8 plus a known nonzero kernel E_A identifies the matrix line, not automatically
metric pose. The checked rank is Fraction elimination, not a Lean rank theorem.

`domain_global_identification.md` gives a complete mathematical sufficient argument for
this11-pair ideal fixture. Zero translation is excluded because two ray pairs change the
squared angular cosine from1/2 to9/10, impossible under a rotation. Any competing
nonzero physical E is then alpha E_A. The left-null condition forces t=tau e1;
entry comparison and SO(3) force R=diag(1,k,k),k=±1. Positive normalized-ray depths
force k=+1; positive horizontal disparity forces tau>0 and fixes all depths to tau
/divided by disparity. Only positive global scale remains. This is an explicit global
argument, not a claim that generic local observability rank suffices.

The full argument has not yet been kernel formalized. A bounded continuation can check
the rank certificate and formalize its rotation-entry argument. Exact rank can be poorly
conditioned under noise; no noisy uniqueness threshold is inferred.

## Verification status and PM recommendation

`domain_planar_poses.lean` compiles10 theorems, including the SO(3) check, positive-depth
existence, both pose equations, essential construction, identities and nonproportionality.
`domain_offplane.lean` compiles4 theorems. `domain_nonplanar_ambiguity.lean` compiles6.
All successful audits use only propext, Classical.choice and Quot.sound. Failed intermediate
attempt logs are retained: matrix/Fin simplification needed refinement, and literal rational
scalar actions in the nonplanar examples required explicit real types rather than accidental
natural-number scalar actions. These were isolated draft statements; no approved theorem
was changed. Linter warnings are retained rather than hidden. Exact Python scripts pass
scoped Ruff checks. Critic was asked to independently compile the final frozen files.

GO for the bounded original-source correction and a certificate-backed ambiguity/selection
fixture, while retaining all admissible pose branches until independent information excludes
them. No general estimator, novelty, physical validation or complete pose-identifiability
classification is claimed. Quality judgment:18/20 (90%) for the bounded review; subjective
confidence high in the exact algebra, with no calibrated confidence assigned to real-camera
transfer. Root owns final scoring and decision.

Final supplement: `domain_cheirality.lean` also compiles3 theorems with only permitted
axioms. It rejects the reversed-translation candidate under positive disparity/depth,
rejects either half-turn candidate using the depth sign, and forces the surviving
translation's depth relation. It does not itself prove that the supplied candidate list
is exhaustive; that is why the global rotation-entry derivation is recorded separately.
The failed initial tactic attempt and successful log are both retained.

Final matrix-identification improvement: `domain_linear_identification.lean` proves,
directly from the11 expanded incidence equalities, that every real matrix fitting the
fixed observations lies in the E_A line. Its sole theorem compiles with only permitted
axioms. This replaces the need to trust numerical rank for that specific conclusion;
the broader SO(3)/scale uniqueness derivation remains hand-derived. The numerical rank
counts for the other fixtures remain Fraction evidence. Three redundant grid assumptions
are unused in the proof, and warnings are retained. Independent coefficient/binding
review was requested. This brings the domain's successful isolated Lean total to24
theorems, without claiming an approved end-to-end estimator.
