# V10 independent critique

The original question has a useful precise answer: fixed-threshold reprojection feasibility is convex when all camera coordinates are affine in the unknowns and each observed depth is positive. This covers fixed-camera triangulation and joint points/translations with fixed rotations. It does not make arbitrary calibrated pose estimation convex.

## Source and model binding

The historical source was a survey, not an existing checked implementation. Kahl's primary paper, section 5.1, explicitly treats fixed rotations with joint camera translations and 3D points, and discusses gauge choices: https://vision.ucsd.edu/sites/default/files/publications/pdfs/Multiple%20View%20Geometry%20and%20the%20L-infinity%20Norm_0.pdf . Hartley and Kahl's author-hosted rotation-search paper separates these convex subproblems from rotation search: https://users.cecs.anu.edu.au/~hartley/Papers/PDF/HartleyKahl%3AEmatrix.pdf . These are established methods; this campaign supplies small checked fixtures and acceptance boundaries, not a novelty claim for SOCP or rotation branch-and-bound.

For a camera vector (a,b,z), observed pixel (u,v), fixed gamma≥0 and z>0, the Euclidean reprojection threshold is equivalent to the cone ||(a−uz,b−vz)||≤gamma*z. Affine residuals/depths interpolate convexly, and strict positive depths remain positive under convex interpolation. Fixed R makes RX+t affine jointly in X and t. Unknown R and X introduce products; calibrated rotation constraints also remain nonconvex. Uncalibrated projective resectioning is not automatically a calibrated SO(3) result. A nonlinear metric-baseline normalization may itself destroy convexity.

## Independently reproduced positives and failures

The domain fixture is calibrated stereo with centers0,e1, observations(0,0),(-1,1/2). Exact vertical residual inequalities give gamma≥1/4; (x,y,z)=(0,1/4,1) attains it. At equality both cone budgets force x=0,z=1, so the point is unique. A coordinatewise norm mutation admits(.1,.25,1), whose Euclidean squared error29/400 exceeds1/16. All nine domain cone lemmas and two generic convexity lemmas independently compile with permitted axioms.

`critic_boundaries.py` and four compiled Lean helpers show:
- Squaring residual inequalities without depth constraints accepts a behind-camera zero-error ray and the zero-depth origin. Strict depth must remain an explicit acceptance condition.
- The variable-threshold epigraph is nonconvex: (x,z,gamma)=(1,1,1),(9,3,3) are feasible, but their midpoint(5,2,2) is not. Quasiconvexity concerns fixed sublevel sets.
- Stereo centers0,e1 with both observed pixels0 has no finite zero-error point, yet every positive threshold g has witness(.5,0,1/(2g)). The infimum0 is unattained. A homogeneous point at infinity is not a finite scene point. A positive lower depth does not prevent escape; an upper depth cap is an added model constraint.
- In a valid rational Cayley rotation chart, known X=e1 and pixel0 have zero error at q=±1/2 with translations(-3/5,∓4/5,1). The chart midpoint q=0 is still a proper rotation, but with midpoint translation has depth1 and error2/5, violating threshold1/10. This is an actual positive-depth pose counterexample, not merely an invalid matrix average.

`critic_replay.py` independently consumes the inventor's two-point fixed-center fixture. Both rational endpoint matrices are proper rotations with positive depths; their convex mean has rank1 and zero error. In the true rotation model, unit columns and the third-row norm imply gamma≥1, attained at the stated positive-sqrt2 rotation. Thus relaxing rotations to their convex hull produces false feasibility even with positive depths. Reflection, center, observation and mean mutations reject. Fixing the camera center matters: free translation would change this problem.

## Rotation-cell route and remaining obligations

The PM's scale-free route is sound as hand norm algebra: for v=R(X−C), v0=R0(X−C), ||R0Rᵀ−I||≤delta, and a true pixel bound, a bound ||v||≤Kz gives k=delta*K<1 and positive nominal depth. With ||[I2,−u]||≤M, the nominal outer threshold is (gamma+M*k)/(1−k). This avoids an artificial world-point norm cap. It preserves the same physical camera center; holding extrinsic translation t unchanged while changing R does not establish this relation.

The proposed fixture constants independently check: U=9/8, M=3/2, K=8/5, delta=1/50, gamma=1/10 give k=4/125 and outer threshold37/242<1/4. Subject to the full camera/operator-norm bridge, nominal infeasibility excludes this entire rotation cell. Outer feasibility does not provide an actual pose. The extension to a complete search still needs authoritative cell coverage, camera/gauge binding, exact lower-bound certificates and checked finite witnesses for upper bounds.

Convexity alone does not guarantee a simple strict dual certificate for every infeasible conic instance, or rational attainment at every boundary. The weak-infeasibility distinction is explicit in [MOSEK’s conic Farkas statement](https://docs.mosek.com/modeling-cookbook/duality.html#infeasibility-in-conic-optimization). Exact validation failure should yield UNKNOWN, not a synthesized infeasibility conclusion from solver status.

GO: a typed threshold/rotation-cell certificate consumer on the declared fixture. HOLD: general search coverage, uncertainty calibration and whole-program/kernel binding. No physical perception or robot claim. Quality17/20; subjective confidence high for the exact fixtures, uncalibrated as a probability.

The physical-center obligation has an exact negative: Rz with c=9999/10001,s=200/10001, X=100e1,t=−RX+e3 has true pixel0 and ||R−I||op²=4/10001≤(1/50)². Using nominal I with unchanged t gives squared image error40000/10001, exceeding the claimed enlarged threshold. The independently checked PM depth module has six permitted-axiom declarations, and the literal domain pixel bridge adds four. Inventor’s five rotation lemmas prove scalar consequences; matrix-to-scalar binding remains explicit hand reasoning.

Independent supplements: all 125 declared Cayley grid matrices were reconstructed through the skew-matrix formula rather than the PM implementation, with exact determinant/orthogonality checks; maximum squared Frobenius distance24/160003 matches. All 36 stored general rectified points were reprojected through the literal cameras. The larger prospective Cayley box ±1/100 has squared Frobenius bound24/10003<1/400; delta1/20 gives outer threshold11/46<1/4. The cutoff3/56 is only a sufficient budget threshold, not the true feasibility transition or largest possible cell. The original survey file still matches its frozen hash.

The inventor’s full-rank convex-hull supplement is also valid by hand: diag(.1,.1,1)R* is a convex combination of two proper rotations but has determinant.01. It exactly predicts pixels±.1 while the proper-rotation minimum is.9 by triangle inequality and the origin-pixel lower bound. Checking only nonsingularity therefore cannot validate the relaxation. This .9 supplement is not included in the five scalar inventor theorem claims.

The general rectified reduction is independently replayed: seven algebraic lemmas plus three literal pixel/converse-realization lemmas. With baselineB>0, s=B/z>0, horizontal disparityd=u1−u2 and vertical mismatchc=v2−v1, the best squared error at fixeds is ((s−d)²+c²)/4. Positive disparity attains the unique inverse depths=d; nonpositive disparity has a strict finite-depth gap above the limit at infinity. The convergence argument remains hand analysis. Two monotonicity lemmas preserve the same witness when increasing the external threshold, without asserting attainment.

Final acceptance:53 independently replayed printed declarations (domain27, critic4, inventor5, PM17), all permitted axiom closures. Private fresh dependency builds used for imported camera modules. Three critic Python scripts pass scoped Ruff and formatting checks. Generic norm transport requires K≥0, delta≥0, gamma≥0 explicitly; all declared numeric constants satisfy these signs. Full hand camera/operator-norm transport is still distinguished from scalar/polynomial kernel proofs.
