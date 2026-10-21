# V10 — fixed-camera cones versus a mixture of rotations

AI-written inventor review. Inherited exact model identifier unavailable. Root owns the600-second review and PM decision. All writes are own `inventor*`; original sources are unchanged.

The main result is an exact counterexample to treating a convex hull of rotations as a calibrated camera: the relaxed problem can have zero error, positive depths, and full matrix rank, while the true SO(3) optimum is9/10. Thus depth positivity and rejection of singular matrices do not repair this relaxation.

## Source recovery and objective

Read the frozen card and `.agents/teamwork/explorer_survey_vision_1/handoff.md`. The survey's broad sentence about converting multiview residuals into SOCP must be restricted by the unknowns, depth domain, and camera calibration.

Inspected the author-hosted [Hartley–Kahl, Global Optimization through Rotation Space Search](https://users.cecs.anu.edu.au/~hartley/Papers/PDF/HartleyKahl:Ematrix.pdf), especially its introduction and fixed-rotation discussion. It explicitly separates convex fixed-rotation subproblems from rotation-space search. Its primary presentation uses angular error on an image sphere and notes image-plane formulations as an alternative. The paper is prior art; no general solver novelty is claimed here. Also inspected the author's institutional [2005 paper listing](https://vision.ucsd.edu/publications/2005/multiple-view-geometry-and-l-infinity-norm), not its full PDF.

Our exact examples use known correspondences and maximum **Euclidean image-plane** error across observations. This is not silently the componentwise infinity norm or angular error. Calibration is fixed to identity. Camera centers/translations are fixed wherever stated.

## Transfer1: conic separation as a small exact safety certificate

Map a fixed camera's bounded image residual to a cone constraint. For known rows p1,p2,p3 and observed pixel(u,v), set `d=p3 Xh`. With d>0,

`||(p1−u p3)Xh, (p2−v p3)Xh||2 <= gamma*d`

is exactly the bounded reprojection condition. At a fixed threshold gamma>=0, the residual vector and depth are affine in a finite point, so adding affine depth/region bounds preserves convexity. The minimax objective is solved through threshold feasibility; gamma and the point should not be treated as jointly affine because their product appears.

The transfer from safety verification is an independently checked witness or separating certificate for the full declared region. A feasible rational point is a positive certificate. A nonnegative combination of valid cone/linear inequalities can prove a threshold impossible. Infeasibility of a conservative outer relaxation is useful; feasibility of that relaxation is not automatically a physical witness.

Falsifiers: change one camera row; reverse a depth sign; permit the homogeneous zero vector; or reuse a threshold certificate after changing calibration. The proof must be rebound to those concrete equations. A squared inequality alone loses the sign of depth. The domain role owns the nondegenerate fixed-camera optimum example, so I did not duplicate its script.

## Transfer2: compactness and infinite-horizon reasoning

Borrow the distinction between a sequence of increasingly good finite witnesses and an attained limiting witness. For fixed cameras `[I|0]`, `[I|−e1]`, both observations(0,0), points `(1/2,0,n)` have error1/(2n). Every positive threshold is feasible, but no finite point has zero error: the first exact ray requires X=0 and the second requires X=1.

Hence the infimum is0 without a finite optimizer. A homogeneous point at infinity can attain the projective limit, but is a different allowed object. Positive projected depth alone does not force a finite affine point. Adding a depth ceiling Z<=D changes this fixture to an attained optimum1/(2D), by `1<=|X|+|X−1|<=2 gamma Z<=2 gamma D`.

This transfer preserves the original finite-point domain while checking which compactness assumption is actually available. The root/critic own the exact depth-cap proof and nonattainment artifact; the derivation here gives its role in a complete algorithm. Falsifier: an optimizer returns threshold0 with no finite point, or returns a homogeneous point with fourth coordinate0 as though it were a finite triangulation result. A finite depth cap is a declared additional assumption, not free numerical regularization.

## Transfer3 (unexpected): randomized-camera mixtures silently change calibration

Treating a rotation variable's convex hull as though it were a physical rotation resembles replacing a deterministic policy by its average. Projection of that average matrix need not be a valid calibrated rigid camera. This is a precise geometric failure, not just the observation that an arithmetic mean can leave SO(3).

Fix camera center0, known world points e1 and e3, and initial observed pixels(0,0) for both. Define the rational proper rotations

```
R+ = [ 3/5  0  −4/5 ]       R− = [ −3/5  0   4/5 ]
     [  0   1    0  ]            [   0  −1    0  ]
     [ 4/5  0   3/5 ]            [  4/5  0   3/5 ]
```

`inventor_rotation.py` checks both row/column orthogonality and determinant1 exactly. Their two point depths are4/5 and3/5, and both have maximum image error4/3. Their equal mixture has only its third row nonzero, `(4/5,0,3/5)`. It belongs to conv(SO(3)), has positive depths for both points, and has zero image error, but determinant0.

The proper-rotation optimum is exactly1. If columns1 and3 of a rotation have depths z1,z3, unit column norms and pixel-error bound gamma imply

`1 <=(1+gamma²)z1²`, `1 <=(1+gamma²)z3²`.

The third row is unit, so `z1²+z3²<=1`. Summing gives `2<=1+gamma²`, hence gamma>=1. The rotation

```
Rstar = [ q  0  −q ]
        [ 0  1   0 ]       q=positive sqrt(2)/2
        [ q  0   q ]
```

attains the bound, with positive depths q and projected pixels(+1,0),(−1,0). Its exact orthogonality, determinant, and projections are verified in the quadratic field Q(sqrt2), with no floating-point trigonometry.

### Stronger full-rank, distinct-observation counterexample

Change the observations to(+1/10,0),(−1/10,0), still with the same known world points and camera center. Every proper rotation has maximum residual at least9/10: otherwise the triangle inequality would give an origin-centered maximum radius below1, contradicting the prior bound. Rstar attains9/10, so this is the exact optimum.

But the convex combination

`M=(11/20)Rstar+(9/20)diag(−1,−1,1)Rstar =diag(1/10,1/10,1)Rstar`

has **zero residual**, positive depths q, and determinant1/100. Both endpoint matrices are proper rotations. Thus M is explicitly in conv(SO(3)) and is full rank; excluding rank-deficient answers does not fix the relaxation.

The left factor is precisely a changed focal scale in this normalized camera form. If calibration were allowed to change, the interpretation would be different. Here calibration is fixed, so the relaxation solves a changed problem. An averaged or blurred exposure might also require a different measurement model; no such model is part of this fixture.

Falsifiers: report relaxed zero error as an SO(3) upper bound; round M to a rotation while keeping the zero residual claim; allow camera translation to vary without changing the certificate; or treat an unknown-focal-length camera as calibrated. The camera-center restriction matters: with free translation toward large positive depth, the two rays can become arbitrarily close, changing the problem again.

## Formal and executable evidence

`inventor_rotation.py/json` verifies the rational rotations, positive depths, exact convex combinations, the Q(sqrt2) attaining rotation, and the full-rank extension. It passes Ruff check and format.

`inventor_rotation.lean` successfully compiles five printed declarations with only `propext`, `Classical.choice`, and `Quot.sound`. Frozen SHA256:

`1b3d249c55df6ce37e26dcf14e5b0c4133b7a8784b47d1674299e90c9e8c6fbd`.

The kernel-checked content is the scalar unit-column/cone implication, universal gamma>=1 consequence, impossibility at gamma1/2, algebraic positive attainer identities, and rational mean-depth arithmetic. The full general Matrix SO(3)-to-scalar binding and the9/10 triangle extension are the explicit hand derivations above, not additional claimed kernel theorems. The initial shell invocation used the wrong relative output path and failed before creating the Lean file; the corrected absolute-path source compiled successfully. No failed result is accepted.

## PM recommendation and precise next test

GO for a fixed-camera certificate consumer with explicit depth/finite-domain assumptions, and for rotation branch-and-bound only with a proper-rotation witness for every reported upper bound. A relaxed feasible camera supplies a lower bound/possible branch, not an admissible upper witness.

The next bounded experiment should feed the full-rank M above to the intended certificate consumer at threshold1/2. A sound calibrated-rotation consumer must reject it despite positive depth and zero residual. It should separately accept Rstar at9/10 for the changed observations, reject a claimed bound below9/10 using the scalar certificate, and preserve the fixed center/calibration in the manifest. Then combine that consumer with the domain role's exact fixed-camera certificate and the root's nonattainment negative.

No full multiview bundle-adjustment solver, outlier-selection theorem, physical camera validation, or new optimization method is claimed. Quality rubric: source binding4/5, mechanisms4/4, decisive tests5/5, independent-check readiness3/3, scope discipline3/3 =19/20. Subjective confidence in the exact fixture and lower-bound argument98%; no success probability is assigned to a general solver.
