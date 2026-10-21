# V03 — cross-discipline inventor

AI-written; inherited root model, exact identifier unavailable. Scope is synthetic calibrated two-view geometry. Root owns elapsed-time accounting and PM decision. No physical movement or source edits.

## Original question and source recovery

When do calibrated correspondences identify a rigid relative pose, and how do planar or zero-baseline scenes affect identification without invalidating the epipolar identity? Sources inspected:

- `/Users/mike/Dev/ctrl-research-notebook/ControlsLean/Vision/Epipolar.lean` proves the incidence identity from a depth-scaled relation over an arbitrary field, requiring only second depth nonzero; R need not be orthogonal. This is a forward identity, not an inverse uniqueness theorem.
- `/Users/mike/Dev/ctrl-research-notebook/docs/proposals/01_planar_homography.md` contains prose saying epipolar geometry is valid only for noncoplanar configurations. That overstates the result and is contradicted by the forward identity and the planar exact examples below. Its discussion of a two-parameter fundamental-matrix family must not be imported unchanged as the ambiguity of calibrated rigid poses.

The correct inverse problem requires nonzero image rays, real SO(3), finite depths, cheirality where physical visibility is claimed, and explicit treatment of global translation scale. Neither determinant zero nor algebraic essential-matrix membership alone proves a reconstructed finite scene.

## Three materially different transfers, plus one unexpected transfer

1. **Control observability modulo gauge.** Pose perturbations correspond to state perturbations; an epipolar residual Jacobian plays the role of an output differential. Translation scale is a known unobservable mode and must be removed before interpreting rank. Preserved: differential distinction of nearby hypotheses. Break: local differential rank does not count disconnected global solutions, and algebraic residuals are only necessary physical constraints. Falsifier: two distinct cheiral rigid poses with full gauge-fixed rank at both. The exact experiment produces precisely this falsifier.

2. **Algebraic elimination with retained side conditions.** Eliminating depth variables produces the epipolar polynomial, analogous to eliminating latent variables in verification. Preserve forward implication; retain nonzero/positive depth and rigid-motion hypotheses in the acceptance certificate. Break: elimination can retain solutions at infinity or lose finite-solvability conditions. Falsifier: pure-rotation correspondences x2=x1, candidate R=I,t=e1. Every epipolar equation holds, but the ray e3 requires impossible finite-depth first-coordinate equality0=1. This is a valid rigid essential matrix that nevertheless does not reconstruct that finite correspondence.

3. **Active identification as branch discrimination.** Treat the remaining physical pose candidates as a version space. An extra observation is valuable when its predicted feasible image sets separate, even if the local rank is already maximal. Preserve the existing camera model and explicitly account for coordinate uncertainty. Break: an added off-plane point can lie in a critical direction and fail to distinguish branches; unknown scene depth cannot be assumed measured. Falsifier: the extra original-pose point at depth2 and v=0 fits both epipolar equations; changing only v to1/3 excludes the displayed alternative. These are synthetic candidate tests, not a hardware action policy.

4. **Unexpected: pose hypotheses as an error-correcting code.** Distinct feasible hypotheses correspond to alternative measurement sets. A measurement is discriminating only when the uncertainty neighborhoods do not overlap. The preserved object is a separation margin, not the numerical size of an unnormalized algebraic residual. Break: the measurement sets contain latent depths and cheirality, so a single codeword per pose would misrepresent the model. For a fixed first ray, distance to the candidate epipolar line is a conservative exclusion measure; lying on the line does not certify physical feasibility. The near-plane noise fixture supplies a concrete overlap witness.

## Exact physical planar ambiguity

The common homography is

H = [[1,0,1],[0,1,0],[0,0,1]].

Pose A: R_A=I, t_A=(1,0,0), scene plane z=1.

Pose B: R_B=[[3/5,0,4/5],[0,1,0],[-4/5,0,3/5]], t_B=(1,0,2), inverse-plane vector m_B=(2/5,0,1/5).

The script checks R_BᵀR_B=I, det R_B=1, and H=R_B+t_B m_Bᵀ exactly. For every ray x=(u,v,1) with u>−1/2, the observed second ray is Hx=(u+1,v,1). Pose A has depth1 in both cameras; pose B has depth5/(2u+1) in both cameras. All depths are strictly positive, and all full 3D equations hold. Thus this is an ambiguity between rigid poses with different rotation and translation direction, not merely the metric translation-scale gauge. The scene planes are unknown and differ between reconstructions; externally supplying the original plane would change the inverse problem.

`inventor_exact.py/json` verifies12 rational rays, with u∈{−1/4,0,1/4,1/2}, v∈{−1/3,0,1/3}. The essential matrices are

E_A=[[0,0,0],[0,0,−1],[0,1,0]],
E_B=[[0,−2,0],[2,0,1],[0,1,0]].

No claim is made that these are the complete solution set.

## Full local rank does not settle global identification

Use left rotational perturbation δR=[ω]×R and free translation perturbation h. The six-column Jacobian uses order(tx,ty,tz,ωx,ωy,ωz). At A its row is

[0,1,−v,−(v²+1),uv,u].

Exact rational row reduction gives rank5 at both A and B. The sole kernel is(h=t,ω=0), the expected translation-scale gauge. Both have t_x=1, so fixing that coordinate supplies a common local chart; the remaining five columns have rank5 at both poses. Exact matrices and RREF are serialized. This verifies a local differential fact while retaining two globally distinct physical reconstructions. It does not prove global uniqueness, a complete multiplicity, noise conditioning, or the absence of other branches.

## Extra observations: rank gain versus branch separation

For an additional point generated under A with first ray(u,v,1) and true depth Z, the second ray is(u+1/Z,v,1). Its E_B residual is

r_B=2v(1−1/Z)=2v(Z−1)/Z,

while r_A=0. An off-plane point at Z=2 gives r_B=v. At v=0, off-planarity alone does not reject B; at v=1/3 it does. This residual vanishes linearly near the original plane or critical image direction. The existing local rank is already5, so demanding a rank increase would incorrectly discard this globally informative observation.

Coordinate uncertainty is explicitly bounded in a second test. Both image rays retain homogeneous third coordinate1, and each of the four finite coordinates can vary independently by ε=1/100. For E_B, triangle inequality bounds the residual perturbation by

ε (||first2(E_B x)||₁ + ||first2(E_Bᵀ y)||₁) +4ε².

At u=0,v=1/3,Z=2, this is7/300+1/2500, strictly below the residual1/3; every coordinate perturbation in the specified box still excludes B. This is an exact algebraic exclusion certificate under the stated noise model, not a statistical probability.

At Z=101/100, the actual second-ray first coordinate100/101 can move to1 within ε. That rounded correspondence is generated exactly by both planar hypotheses. Thus a physically off-plane point does not guarantee robust discrimination at finite precision. The shared-coordinate-error assumption is part of this synthetic test; real calibration and correlated feature errors need their own model.

For a known exact first ray at u=0, candidate B's line coefficients are(−2v,1,v). Its exact target-image ℓ∞ distance is |r_B|/(2|v|+1). This ratio is invariant to rescaling E_B and is a more meaningful pairwise separation score than raw residual magnitude. It is still only a necessary-geometry rejection bound, not a sufficient positive reconstruction certificate.

## Gate recommendation, critique and next action

GO for a bounded certificate interface that distinguishes: forward identity; physical candidate feasibility; gauge-fixed local rank; global candidate set; and measurement discrimination margin. Next test: independently reproduce the positive-depth ambiguity, include the zero-baseline finite-depth counterexample, and package an interval-certified rejection of the displayed alternative under bounded image errors. Require the independent checker to inspect full scene equations and R∈SO(3), not only epipolar residuals. Formalization should preserve original approved challenge statements.

HOLD any claim of global pose uniqueness, complete homography decomposition, unknown-intrinsic robustness, active robot motion safety, or general sensor-placement optimality. Those need additional proofs or models. No literature novelty claim is made; these are constructive source corrections and crossover diagnostics.

Evidence: exact rational arithmetic plus elementary derivation, not kernel proof or physical validation. Quality rubric: faithfulness4/4, reproducibility4/4, discriminatory value4/4, critique3/4, actionability3/4 =18/20 (90%). Subjective confidence: high in the finite exact fixtures; no calibrated confidence assigned to generalization.

## Adversarial full-lift follow-up

The Z=2,v=0 off-plane example above is only an epipolar residual test: candidate B's lift forces first depth0 and second depth2, so it fails physical cheirality. This is itself a useful negative control for an identity-only checker.

A stronger replacement preserves physical ambiguity after adding an actually off-plane point. Take x1=(0,0,1), x2=(2/3,0,1). Pose A uses depth pair(3/2,3/2), so the scene point lies off the original z=1 plane. Pose B uses depth pair(5/6,5/2). The exact script checks both full rigid equations and all four strict depth inequalities. Hence even an extra noncoplanar point can fail to distinguish the displayed rigid poses when its image direction is critical. It is the physical depth3/2 fixture, not the algebraic-only depth2 fixture, that supports this stronger statement. This upgrade also demonstrates why the proposed certificate must check scene lifts after residuals.

The pair's algebraic critical variety can be derived directly. For an A-world point(X,Y,Z), Z≠0, substitute x1=(X/Z,Y/Z,1) and x2=((X+1)/Z,Y/Z,1): r_B=2Y(Z−1)/Z². Hence the zero locus is the union of planesZ=1 andY=0. Cheirality still has to be checked separately. To avoid confusing positive depth with visibility, the final script adds two off-plane points (X,Y,Z)=(±1/10,0,3/2) and verifies positive full lifts under B and distinct first and second rays from every original planar correspondence. These preserve both reconstructed poses while the original planar subset already supplies local rank5. This is a sparse point-scene fixture; opaque surfaces and occlusion are not modeled. Repeated points at different depths on the same axial ray would not establish simultaneous visibility and are not used for that claim.

The final14-correspondence fixture has distinct rays in each camera. Its exact six-parameter residual rank remains5 at both reconstructed poses. Four-point affine determinants are1/6 under A and−62500/741 under B, certifying noncoplanarity in both reconstructed scenes. The full point coordinates and determinants are serialized under `augmented_fixture`. Thus neither cheirality, distinct rays, noncoplanarity, nor full gauge-fixed local rank—taken together—establish global uniqueness for this deliberately critical fixture.

## Small minors and conditioning certificate

`inventor_conditioning.py/json` reduces the tangent-rank witness to first-image points(0,0),(1,0),(0,1),(1,1),(0,2). Columns are(ty,tz,ωx,ωy,ωz), with t_x fixed to remove scale. At the original poses the5×5 determinants are2 at A and6 at B. These explicit small matrices offer a simpler independently checked certificate than trusting a general rank routine.

A rational family separates exact observability from a usable margin. Keep pose A's translation fixed at the unit vector e1 and move the scene plane to depth1/β, β>0. Then the correspondence is(u,v,1)→(u+β,v,1), and the A Jacobian row is[β,−βv,−(v²+1),uv,u]. Its determinant on the five points is exactly2β²: the first two columns each factor β, leaving the verified constant determinant2. Thus rank5 persists for every nonzero β. The squared norm of its ty column is5β², while the squared norm of its ωx column is35. Rayleigh bounds imply σ_min²≤5β², σ_max²≥35, and condition-number²≥7/β² in this specified chart and residual normalization. Global rescaling of E cancels from the ratio; arbitrary state or per-row reweighting changes the conditioning interpretation.

The script checks β=1,1/2,1/10,1/100, constructs the corresponding second proper rotation and positive depths, and records both minors. The last condition-number lower bound squared is70000 despite exact rank5. The limit takes nonzero translation with scene depths tending to infinity; it is not itself a finite zero-baseline scene. This gives a precise control-observability lesson: certify both rank and a numerical or interval margin before describing a reconstruction as well-conditioned.

## Linear matrix rank and exact branch classification

The9-column unconstrained epipolar design matrix has ranks6 for the planar12 rays,7 after the two noncolliding critical off-plane rays, and8 after a fifteenth ray x1=(0,1/2,1), x2=(1/2,1/2,1). The final ray is distinct from every existing ray in both cameras. Matrices and RREF are serialized. Rank8 identifies a nonzero epipolar matrix up to scale, but does not alone establish a physical rigid-pose reconstruction or exclude E=0.

The rank7 critical case can be classified explicitly. All planar matrices have the form F=[e]×H for e=(a,b,c). A nonplanar critical-plane point forces b=0, leaving

F=[[0,−c,0],[c,0,c−a],[0,a,0]].

Its Gram matrix has eigenvalues0, c²+a², c²+(c−a)². The two nonzero values are equal precisely when c(2a−c)=0. Excluding the zero matrix, this leaves exactly the two projective essential-matrix classes already constructed: c=0 gives E_A and c=2a gives E_B. The script verifies the Gram algebra and positive/negative rational controls; the polynomial factorization is an elementary derivation. This classifies essential matrices for this exact dataset, not a complete pose decomposition. It makes no novelty claim about critical varieties.

For the rank8 data, a separate pure-rotation exclusion is available from two original ray pairs: squared inter-ray angle cosines are9/10 before and18/19 after. A rotation preserves these, so no t=0 reconstruction can fit them. Root/domain are independently checking the remaining special-E_A pose-completeness argument; it is not claimed as a kernel result here. The next formal acceptance target should bind all three layers—matrix nullspace, SO(3) decomposition, and positive scene lifts—rather than promote rank8 by itself.

Current checks: both inventor scripts execute successfully with exact rational arithmetic, and both pass Ruff lint and formatting. No integrated repository code changed.

An alternative matrix-family certificate avoids a general rank theorem. On planar correspondences, the generic F residual is the quadratic with coefficient vector

(f00, f01+f10, f11, f00+f02+f20, f01+f12+f21, f02+f22)

in monomial order(u²,uv,v²,u,v,1). The six existing points(0,0),(1/4,0),(1/2,0),(0,−1/3),(0,1/3),(1/4,1/3) give an evaluation matrix of exact determinant1/5184. Consequently, zero residuals on just these six points force all six coefficients zero and yield F=[e]×H directly with e=(f21,f02,−f01). The nonplanar critical observations then force b=0, and the final transverse point forces c=0. The interpolation matrix, coefficient map, and determinant are in `inventor_conditioning.json`; all nine matrix basis elements were checked independently against the residual expansion. This is a smaller prospective formal certificate for matrix-family completeness than the15×9 RREF.

A final coefficient certificate removes the sampled-only limitation for the second pose's minor. `inventor_polynomial.py/json` expands the5×5 determinant directly as polynomials and verifies det J_B=2β⁴(β+2) after clearing the positive denominator(4+β²)⁵. Its matrix entries are also checked against all four independently generated rational Jacobian fixtures. Therefore both pose minors are nonzero throughout β>0, while the A conditioning bound still degrades without bound as β→0. This is exact polynomial arithmetic, not a solver status or Lean result. All nine small rational determinant certificates were additionally cross-checked using both Gaussian elimination and direct permutation sums.
