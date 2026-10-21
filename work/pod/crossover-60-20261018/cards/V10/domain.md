# V10 domain review — bounded reprojection feasibility

AI-authored domain research; inherited root model, exact identifier unavailable. Only isolated campaign domain files were created. Original survey/source files and approved challenges are unchanged.

## Recovered question and primary-source scope

The frozen question asks which maximum-reprojection-error subproblems admit convex feasibility certificates under positive depth, with fixed versus unknown rotations. The original handoff is a survey, not a previously implemented conic solver or a checked general pose theorem.

The [Kahl–Hartley 2008 author/institution record](https://portal.research.lu.se/en/publications/multiple-view-geometry-under-the-l-infinity-norm/) describes quasiconvex reformulations for triangulation, camera resectioning and homography estimation using SOCP. This supports the historical method, not a novelty claim for this campaign.

The [Hartley–Kahl rotation-search author PDF](https://users.cecs.anu.edu.au/~hartley/Papers/PDF/HartleyKahl:Ematrix.pdf), sections1.2–2, separates fixed-rotation convex feasibility from search over rotations. Its main calibrated formulation uses angular error on the image sphere; it discusses known-rotation pose/structure-motion and rotation branch-and-bound. Its existence discussion admits oriented projective points at infinity and supplies special conventions at camera centers. These conventions must not be silently imported into a finite, strictly positive-depth image-plane problem. The paper also distinguishes its LP relative-pose reduction from generic SOCP. The UCSD-hosted earlier PDF returned an unavailable content response in this session; no claim of reading that full paper is made.

## Exact affine denominator criterion

For fixed camera P and finite point X, let its three camera coordinates be affine functions a(X), b(X), z(X). For observed image pixel (u,v), positive depth z(X)>0, fixed threshold gamma≥0, and Euclidean pixel error,

    sqrt((a/z-u)^2 + (b/z-v)^2) ≤ gamma
    iff sqrt((a-u*z)^2 + (b-v*z)^2) ≤ gamma*z.

The numerator vector and right side are affine in the optimization variables. The norm triangle inequality therefore proves convexity of each fixed-threshold sublevel set, and intersections preserve it. Strict positive-depth halfspaces are convex too, but open: an ordinary closed cone feasibility program may admit z=0 when its numerator vanishes. A proposed solution must separately certify positive depth, or use an explicitly justified positive-depth margin. Squaring loses the sign and zero exclusions, so a squared residual inequality alone is not a visibility certificate. Threshold gamma is held fixed; joint minimization over gamma and depth introduces their product and is not thereby a convex program. Bisection exploits nested feasible sublevels instead.

This criterion applies to fixed-camera triangulation. With fixed rotations and calibration, joint points and translations also enter R_i(X_j−C_i) affinely, so the same threshold constraints apply subject to appropriate affine gauges and depth restrictions. A unit-baseline equality is not an affine gauge; adding it can spoil convexity. Replacing arbitrary physical calibrated-camera constraints by free entries of a projective camera matrix also changes the question, even when the resulting resectioning problem is quasiconvex.

Unknown rotations restore SO(3) and, with unknown points/centers, products of unknowns. A fixed-rotation feasibility certificate certifies that rotation only. A global search requires a proved relaxation/lower bound valid over an entire rotation cell and complete coverage of the rotation domain. Replacing all rotations in a cell by its center is not such a bound. Root and other roles test these boundary cases separately.

## Exact fixed-camera fixture

Take calibrated cameras P1=[I|0] and P2=[I|(-1,0,0)], known metric baseline1, observed pixels (0,0) and (-1,1/2), and world point (x,y,z), z>0. The two numerator residuals are

    (x,y), (x+z−1,y−z/2).

Cone feasibility at threshold gamma implies y≤gamma*z and z/2−y≤gamma*z. Adding gives gamma≥1/4. Thus gamma=1/5 is infeasible by an exact scalar inequality certificate, independent of any optimizer. Point (0,1/4,1) achieves gamma=1/4. At that threshold the vertical inequalities force y=z/4; each Euclidean norm budget is then saturated vertically, forcing x=0 and x+z−1=0. Hence z=1 and the optimum is unique among finite positive-depth points for these fixed cameras.

`domain_cones.lean` proves nine declarations: denominator scaling, squared threshold equivalence, signed vertical bounds, global lower bound, attainment, threshold1/5 infeasibility, uniqueness, and the Euclidean square-root/cone equivalence. `domain_convex.lean` proves norm-cone interpolation and positive-depth interpolation. The norm interpolation theorem is generic, not an assertion that every camera parameterization is affine. The affine camera binding above is explicit algebra.

`domain_pixels.lean` adds the direct literal image-plane formulas and binds them to these cones, then proves global bound, unique optimum and attainment. This removes dependence on a reader trusting the hand expansion of the two residual numerators. Compilation status is recorded separately; only successful frozen declarations are accepted.

`domain_exact.py/json` independently evaluates rational residuals. A deliberate norm mutation is informative: point (1/10,1/4,1) has coordinate-wise maximum error1/4 but squared Euclidean error29/400>1/16. It therefore does not attain the declared Euclidean optimum. Calling both criteria “L-infinity reprojection” without specifying the per-observation norm would incorrectly preserve the optimum's uniqueness claim. The maximum across observations and the Euclidean norm within each observation are separate choices.

## Verification and limits

Initial local cone/convex compilation passes11 declarations with only propext, Classical.choice and Quot.sound; first cone draft failed on an unnecessary tactic after an already-closed goal, and that log is preserved. No solver is used. The role's exact script is checked with scoped Ruff. The direct-pixel wrapper is a separate frozen module for independent replay. The critic's four boundary lemmas were independently compiled by this role in `domain_critic_boundaries.log`: fixed-camera zero-error infeasibility with arbitrary positive thresholds feasible, nonconvex variable-threshold epigraph, and missing-depth counterexamples. These proofs expose distinct domain issues; they do not invalidate fixed-threshold convexity.

GO for an exact certificate interface with fixed norm/camera/depth/gauge semantics, primal positive-depth witnesses and exact separating inequalities. HOLD on general unknown-rotation certification until every rotation cell's conservative bound and global cover are supplied. A finite branch-and-bound run's conclusion is only as strong as its coverage, cell bounds, and termination tolerance. No full SOCP implementation, generic global rotation optimizer, physical camera calibration or new vision theorem is claimed.

Next test: export a tiny fixed-camera feasible/infeasible certificate together with camera and observation hashes, then mutate the baseline sign, depth sign, per-pixel norm and one camera rotation. Each mutation must either be rejected or produce a newly checked theorem for the altered problem. The exact fixture gives an analytic oracle for that test.

Quality:18/20 (faithfulness4, reproducibility4, discriminatory value4, critique3, actionability3),90%. Subjective confidence is high for the bounded algebra and local kernel proofs; confidence in a complete global-rotation solver is not assessed.

The four literal-pixel wrappers now compile exit0 with standard axioms. `domain_nested.lean` additionally records threshold monotonicity for a norm cone and for any family of views with unchanged admissibility/gauge predicates and positive depths. It preserves the same witness when the threshold increases. This is the bisection nesting obligation; it asserts neither compactness nor attainment of an infimum. Final compilation/replay hashes are tracked in `domain_acceptance.json`.

## General rectified-stereo admission rule

For baseline B>0, measured disparity d=u1−u2, vertical difference c=v2−v1, and inverse depth parameter s=B/z>0, write the two residuals as (a,b) and (a−(s−d),b−c). The sum of their squared Euclidean lengths is

    2*((a−(s−d)/2)^2+(b−c/2)^2) + ((s−d)^2+c^2)/2.

Thus their maximum squared error is at least `((s−d)^2+c^2)/4`. Balanced residuals attain that bound. For every s>0 this balanced pair is realized by a finite positive-depth point:

    z=B/s, x=z*(u1+(s−d)/2), y=z*(v1+c/2).

If d>0, s=d is feasible and uniquely minimizes the reduced scalar objective, giving z=B/d and error |c|/2. The residual midpoint is unique as well, including c=0. If d≤0, every s>0 has strictly larger squared error than (d²+c²)/4, while the gap `(s²−2*s*d)/4` tends to zero as s→0. Hence the finite-depth infimum is sqrt(d²+c²)/2 and is not attained. The convergence sentence is elementary analysis recorded by hand; the exact gap, strict inequality and positive-disparity scalar classification are in `domain_rectified.lean` (seven successfully compiled lemmas). This is a complete reduction for this specific rectified two-camera structure, not arbitrary multiview geometry or unknown rotations.

`domain_rectified_pixels.lean` separately binds the literal pixel differences, derives the reduced bound from actual squared pixel inequalities, and constructs the finite balanced point. Acceptance is contingent on its recorded successful compile and independent replay. `domain_rectified_exact.py/json` tests36 rational realizations over positive, zero and negative disparity, multiple vertical differences and inverse depths. These are independent arithmetic checks; universal optimality comes from the algebra, not a grid search.

Final local status: all27 domain declarations across six Lean files pass with allowed standard axioms, including the three general literal-pixel reduction lemmas. Independent critic acceptance remains separately recorded by that role. All two domain Python scripts pass scoped Ruff, and original files remain unchanged.
