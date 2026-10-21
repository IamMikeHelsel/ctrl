# V12 domain: exact planar-calibration acceptance

AI-written; inherited root model, exact identifier unavailable. Original proposal01_planar_homography.md only cites Zhang calibration as an application. Its homography/epipolar claims do not establish calibration identifiability. Known planar-scene prose errors were addressed in V03 and are not reused here. Original sources remain unchanged.

Primary source inspected: [Zhang, Microsoft Research TR98-71, updated2008](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr98-71.pdf), especially §§2.2–3.1. The paper derives two homogeneous intrinsic constraints per planar view. Its full five-intrinsic linear solution needs at least three generic views; the two-view variant adds a zero-skew condition. The abstract's 'at least two' is therefore not an unconditional full-intrinsic identifiability claim. Distortion/refinement are separate from its initial linear solve. Our exact tests below are familiar calibration algebra and are not claimed novel.

## Model and certificate

Use a fixed undistorted pinhole matrix K, upper triangular, positive diagonal and K33=1. Each metric checkerboard view has H=λK[r1 r2 t], λ≠0, where r1,r2 are orthonormal columns of a proper rotation. Set B=K⁻ᵀK⁻¹. Its six independent entries are ordered(B11,B12,B22,B13,B23,B33). Orthogonality and equal lengths give h1ᵀBh2=0 and h1ᵀBh1−h2ᵀBh2=0. The coefficient row for columns x,y is

    (x1y1,x1y2+x2y1,x2y2,x3y1+x1y3,x3y2+x2y3,x3y3).

Stack the two rows per view into A. A rank-five exact system has a one-dimensional nullspace; it determines B only up to scale. Choose its sign/scale to be positive definite, then recover normalized K by triangular factorization. Rank alone is not enough: indefinite B cannot be a Euclidean intrinsic metric. Rank six means no exact nonzero common B. Rank below five plus an existing positive-definite solution admits a local continuum of positive-definite solutions, because positive definiteness is open. Additional declared intrinsic assumptions can change this count.

A proof-carrying exact result can include the literal homographies and board metric model, A, a row-reduction certificate U and inverseU⁻¹, RREF/pivots, normalized null vectorb, and a positive-definite factorization of B. Check U A=RREF and U⁻¹U=UU⁻¹=I, not a producer's rank assertion. Then independently check pose rotations, common scale, image correspondence consistency, and depth over the intended board. Noisy data generally make A full rank; exact rank cannot be naively reused as a noise-robust acceptance test.

## Exact nonzero-skew fixture

Predeclared intrinsics:

    K=[[2,1/2,1],[0,3,−1],[0,0,1]].

Use I, an x-axis rotation with cos3/5,sin4/5, and a y-axis rotation with cos5/13,sin12/13. Viewj has translation(j/4,−j/3,4+j). The whole board[-1,1]² has positive depth, checked at the affine depth's four corners. Explicit rotations have determinant+1 and are orthogonal; their matrix products are checked exactly. The fixture input is an exact homography, not a claim that a detector recovered it from pixels.

Results from domain_rank.py/json:

- Three fronto-parallel views, including distinct in-plane rotations and translations: rank2.
- The two tilted views: rank4.
- Identity plus both tilts: rank5.

The rank-five normalized solution B11=1 is

    b=(1,−1/6,17/36,−7/6,23/36,209/36)=4 vec(K⁻ᵀK⁻¹).

Its quadratic form is exactly

    (x−y/6−7z/6)²+(2y/3+2z/3)²+(2z)²,

which is strictly positive for every nonzero vector. `domain_binding.lean` checks the coefficient-row interpretation, homography squared-scale algebra, this SOS identity, and strict positivity. `domain_rank.lean` checks that the six explicit view equations and gaugeB11=1 force exactly this six-tuple over arbitrary real inputs. This concrete linear uniqueness proof is stronger than merely recording the numerical rank. General Cholesky reconstruction and arbitrary-view rank semantics are hand-described, not silently claimed formalized.

## Physical ambiguity, not just a nullspace count

`domain_fronto.py/json` constructs a second physical camera for all three fronto-parallel views:

    Kalt=K diag(2,2,1), same rotations, talt=(tx,ty,2tz).

The resulting homographies equal2H exactly, hence yield identical images of every board point, with positive depth. Focal scales and skew change, while unknown camera-to-board distance compensates. More translations or in-plane rotations do not remove this ambiguity. This does not assert that all three-view configurations fail or that different tilt axes are necessary; the actual rank check is the criterion.

## Two tilted views: positive metric ambiguity

`domain_two_views.py/json` adds an exact null direction `(0,−24,8,30,3,−20)` to the normalized metric, scaled by1/1000. Both the original and modified metrics satisfy every equation for the two tilted views, have B11=1, and differ. The alternative leading principal minors are exactly1,62419/140625,4081/2250, so Sylvester's criterion certifies positive definiteness. This example cannot be rejected merely by adding an SPD check.

A further semantic mutation falsely assumes zero skew. The same family at coefficient−1/144 gives `(1,0,5/12,−11/8,89/144,107/18)` with positive leading minors1,5/12,847/648, while still satisfying both tilted views. This produces a physically admissible but wrong camera for the predeclared true K. Added intrinsic priors require external justification; exact consistency cannot verify them.

The physical reconstruction implication is hand mathematics, explicitly outside the Lean suite. For an SPD B consistent with the two rows of each nonsingular H, choose normalized positive upper-triangular K with K⁻ᵀK⁻¹=cB, c>0. Let λ=√(h1ᵀK⁻ᵀK⁻¹h1)>0, r1=K⁻¹h1/λ, r2=K⁻¹h2/λ, r3=r1×r2 and t=K⁻¹h3/λ. The two constraints give orthonormal r1,r2, so these columns form an SO3 rotation and H=λK[r1 r2 t]. Because normalized K has bottom row(0,0,1), reconstructed depth at a board point is the original homography denominator divided by positiveλ. Our fixtures' positive denominators therefore remain positive for either metric. Distinct normalized B imply distinct normalized K. Thus this exact ambiguity is physical under the stated pinhole assumptions, not a spurious indefinite algebraic solution. General factorization/pose reconstruction is not kernel-checked here.

## Acceptance scope and next action

GO for an exact rank/SPD/pose certificate checker bound to metric board coordinates. Frontality/poor excitation is a meaningful admission rejection. HOLD robust camera calibration until explicit image uncertainty, distortion, board accuracy, normalized residual and conditioning contracts are supplied. A successful homography theorem or a small algebraic residual alone is insufficient. Inventor/critic's indefinite rank-five fixture and root's near-fronto-parallel noise fixture are complementary required negatives.

Producer files retain an initial failed rank proof log; corrected acceptance requires exitzero and standard axioms. No whole notebook rebuild, physical calibration, detector accuracy, or new calibration algorithm is claimed. Quality18/20(90%); subjective confidence high in the exact fixture, with noisy inference and general reconstruction outside this bounded result.
