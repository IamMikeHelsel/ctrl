# V01 domain — from source coordinate identities to genuine image rays

AI-written; inherited root model, exact identifier unavailable. All owning source files and toolchain pins remain unchanged. Classical projective geometry is not claimed as a new result.

## Source and proof boundary

The actual `ControlsLean.Vision.Homography` proves coordinate-vector identities over an arbitrary field. Its plane transformation is H=R+d⁻¹tnᵀ. The source `plane_homography_constraint` proves d2 x2=H(d1 x1) from the plane and affine-motion equations. It does not itself assert nonzero image rays, nonzero second depth, positive depths, invertibility of H, finite affine image coordinates, or calibration matrices. Nor does it assume R is orthogonal or n is unit length. Accordingly, d is an algebraic plane offset; calling it perpendicular distance requires a unit-normal convention outside that theorem. Calling R a rigid rotation also requires extra assumptions. These broadened algebraic statements are valid; the stronger prose interpretations need explicit conditions.

The source proposal's claim that epipolar geometry is invalid for planar scenes is incorrect; V03 separately examined that distinction. Homography does not make the epipolar identity false or establish pose uniqueness. Here we focus on valid nonzero ray and chart transfer.

Original source pin is Lean4.36.0-rc1. The compiler is installed, but its notebook Mathlib compiled cache and local Vision oleans are absent. Root authorized an isolated replay using the existing4.33 Mathlib cache. `domain_source_replay.py/json` freshly builds byte-identical Epipolar and Homography copies, checks before/copy/after hashes, and leaves originals and pins unchanged. This is explicitly not a successful original pinned4.36 build. New domain modules import those actual source declarations, rather than renamed restatements.

## Nonzero and scalar gates

`domain_rays.lean` proves five source-bound lemmas. The existing plane assumption n·(d1 x1)=d≠0 already implies n≠0, x1≠0 andd1≠0; these need not be redundant new hypotheses. If d2≠0, the source relation gives

    x2=(d1/d2) Hx1, with d1/d2≠0.

This scalar relation alone does not make x2 a genuine ray: a singular H can send x1 to zero. A left inverse G H=I prevents zero images and, together with the source plane/motion relation, forces both d2≠0 andx2≠0. The source incidence identity also survives independent nonzero rescalings of line and point representatives.

`domain_projective.lean` supplies the missing representative logic: H p=cH q iff p=cq whenG H=I, and nonzero line vectors remain nonzero under the source Gᵀ action. Restricting c to nonzero scalars gives preservation and reflection of the projective equivalence relation on nonzero vectors. No actual Quotient type or complete projective-space API is constructed here. Positive orientation still requires an ordered field and positive representative/depth conventions. Finite normalized pixels separately require a nonzero third component. These conditions cannot be recovered from an arbitrary-field scalar identity.

## Exact invertibility criterion

`domain_determinant.lean` uses the source outer product and plane-H definition. For any y withRy=t,

    H=R(I+d⁻¹ynᵀ),
    detH=detR(1+d⁻¹n·y).

If detR≠0 andd≠0, H is singular exactly when n·(−y)=d. SinceR(−y)+t=0, −y is camera2's center expressed in camera1 coordinates. Thus the plane must avoid both camera centers for a global invertible plane-to-image projectivity. The first exclusion isd≠0; the second isd+n·y≠0. Merely having some positive-depth correspondences does not imply the second exclusion. Critic owns the exact R=I,t=−e1,n=e1,d=1 singular fixture with two valid positive-depth source rays collapsing to one image ray.

The determinant proof is over the actual arbitrary-field matrix declarations; it does not silently assume SO3. `domain_exact.py/json` independently checks81 rational cases, including12 singular cases, over two proper rotations and a clearly labeled nonrigid affine diagnostic. Every case checks both determinant criterion andHX=RX+t on a constructed plane point. These exact checks are regression fixtures, not a replacement for the generic kernel theorem. The first Lean draft failed a matrix-lemma qualification and scalar sign; the failed log is preserved, and the repaired module compiles.

## Calibration bridge

`domain_pixels.lean` makes the missing intrinsic matrices explicit. WithK1inv K1=I, p1=K1x1 andp2=K2x2, the source relation implies

    p2=(d1/d2)(K2 H K1inv)p1.

The algebraic transport lemma does not claim K2 is invertible. For physical nonzero pixel rays, invertible intrinsic matrices and the earlier ray gates must be supplied. It does not divide by a pixel's third coordinate or claim a numerical stability margin. Those are separate chart/conditioning checks investigated by inventor and PM.

## Next action and evidence

GO for a source-bound camera adapter that checks plane offset, camera-center exclusion, calibration inverse identities, nonzero rays, positive depths where required, and an affine-chart margin before applying downstream image constraints. HOLD a fully constructed projective quotient and physical camera calibration interface until those APIs and actual input semantics are bound. NO-GO for treating the existing unconstrained vector identity as a global positive-depth finite-pixel guarantee.

Primary author-hosted reference checked: [Hartley–Zisserman second-edition chapter index](https://robots.ox.ac.uk/~vgg/hzbook/hzbook2/HZfigures.html) identifies chapter13 as scene planes and homographies; [author-provided geometry code](https://www.robots.ox.ac.uk/~vgg/hzbook/code/) lists the two-camera/plane homography routine. No detailed theorem text was available from those index pages, so the algebraic criterion above is our explicit derivation, not a quotation or a claim of new geometry. Quality18/20(90%); subjective confidence high for the scoped algebra, with chart/physical and original-pin gaps explicit.

Acceptance: all15 domain declarations producer-compile with only standard axioms, and were frozen for independent critic replay. Critic_collapse3 independently compiled with exit0 and matching source hash; its first two lemmas bind the positive-depth singular physical pair, while its third checks determinant values with the connecting diagonal map hand-bound. Scoped Python Ruff check and formatting pass. Root gauge/patch statements were independently read: gauge cancellation at zero denominator is only total-field algebra; the separate positiveheight guard is required for a usable finite-pixel chart.
