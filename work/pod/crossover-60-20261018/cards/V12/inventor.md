# V12 inventor — metric admission before calibration confidence

AI-written by the cross-discipline inventor; inherited root model, exact identifier unavailable.
Original question: which metric planar checkerboard views determine a common pinhole intrinsic
matrix, and what check should accompany that claim? The source proposal only catalogues Zhang
calibration; it does not contain an implemented estimator or empirical camera acceptance.

Primary source consulted: Zhang's author technical report,
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr98-71.pdf,
§§2–3: H is proportional to K[r1 r2 t]; orthogonality and equal rotation-column norms give
two homogeneous linear constraints on B=K^-T K^-1 per view. Three suitable views give five
independent constraints. This exact undistorted linear initialization is distinct from the
report's later image reprojection refinement and distortion treatment.

## Three transfers, with preserved objects and falsifiers

1. **Persistent excitation and gauge-aware experiment design.** The control-theory object is
an identifiable parameter quotient; here it is symmetric B modulo overall scale. Stack the
view constraints and ask which view removes a remaining null direction. Rank is preserved
by a nonzero homography rescaling, but raw residual magnitude and Gram eigenvalues are not.
The exact test rescales one H by -3, 1/100, and 100: image points remain unchanged, its two
constraint rows scale by lambda², and its Gram contribution by lambda⁴. Thus raw conditioning
cannot be compared before fixing homography normalization and a noise model. Repeating the
same rows three times does not add rank; correlated reuse cannot be called new independent
sensor information. Falsifier: an acquisition score that declares a view more informative
solely after arbitrary projective rescaling. A noise-whitened score needs the uncertainty
transformed with the representation, not an invented universal normalization.

2. **Proof-carrying calibration as a typed physical admission check.** Transfer the compiler
idea that a syntactically valid object must also satisfy semantic invariants. Preserve the
actual six B coordinates, view matrices, five-dimensional rank certificate, and the
positive-definite camera metric. Exact negative below passes rank and homogeneous consistency
but fails physical metric admission. A next consumer should check the supplied homographies,
recompute rows, validate rank/nullspace, test SPD up to allowed scale, reconstruct normalized
K, and check source-bound proper pose and board-corner depths. Falsifier: accept our rank-five
indefinite fixture, or accept a stale certificate after changing a homography. Positive
projective denominators alone are not a substitute for the Euclidean reconstruction.

3. **Unexpected transfer: calibration-target metrology as gauge fixing.** The checkerboard
is an input standard, analogous to an instrument's calibration ruler, not an error-free
semantic fact inferred from its own images. Exact one-view diagnostic: actual camera K=I,
frontoparallel plane at depth1, true target coordinates (2X,Y), produce exactly the same
pixels as a nominal square target (X,Y) and inferred K=diag(2,1,1). This preserves pixel
correspondence but changes the asserted metric target. It is explicitly a rank-deficient
one-view alias, not a claim that generic multi-view tilted calibration cannot detect target
anisotropy. A uniform global target rescaling instead changes extrinsic translation scale
without changing K. Falsifier for a proposed acceptance contract: swapping a rectangular
print for the assumed square target must either fail a declared target-metric check or remain
outside its guarantee. Next experiment: carry target metric intervals into the multi-view
feasibility set rather than silently assigning all residual to the camera.

## Exact discriminator

`inventor_metric.py/json` constructs

- H0=diag(1,1,5),
- Hx with columns (5/3,0,4/3), (0,1,0), (0,0,5),
- Hy with columns (1,0,0), (0,5/3,4/3), (0,0,5).

Their determinants are 5,25/3,25/3. Every denominator on the declared square [-1,1]^2 is
at least 11/3. The 6x6 calibration matrix has exact rank5 and nullspace
span{(1,0,1,0,0,-1)} in order B11,B12,B22,B13,B23,B33. Thus B is proportional to
diag(1,1,-1), which has no positive-definite nonzero scaling. These are well-defined planar
projectivities; they are deliberately not certified common-intrinsic Euclidean camera views.
The negative separates projective consistency from physical intrinsic consistency.

`inventor_indefinite.lean` proves the literal six constraints force B22=B11 and B33=-B11,
and consequently cannot satisfy the necessary positive quadratic forms on both x and z axes.
This is a concrete scalar certificate, not a formalized general camera reconstruction theorem.
Compilation status and axiom audit are recorded in its adjacent log.

## Gate and limits

Suggested GO: a small calibration acceptance consumer combining the domain's genuine rational
camera fixtures with this indefinite false-pass and homography-scale metamorphic tests.
Next bounded test: reject altered rows, missing view provenance, indefinite/singular B and
nonphysical pose reconstruction; accept the exact domain fixture, then exercise bounded
homography uncertainty with a declared normalization. A rank threshold alone is NO-GO as
physical calibration acceptance. No novel calibration theorem, noisy image guarantee,
real checkerboard collection, lens-distortion model, or physical validation is claimed.

Quality judgment: 18/20 (faithfulness4, reproducibility4, discriminatory value4, critique3,
actionability3); subjective confidence98% in exact algebra, ungraded physical applicability.

## Gauge-invariant coverage supplement

`inventor_projector.py/json` constructs P=Aᵀ(AAᵀ)^-1 A for each rank-two view block A.
In the declared Euclidean six-coordinate chart, P is symmetric and idempotent, has trace2,
and projects onto that view's constraint space. Nine exact homography-rescaling tests and
three invertible row-generator changes leave P identical, although raw Gram traces change
by lambda⁴. The sum has the same null intersection as all views: bᵀ(ΣP)b=Σ||Pb||².
This offers a geometry-only rank/coverage discriminator before choosing a statistical model.
It intentionally gives up measurement magnitude and precision; it is not a covariance or
Fisher-information replacement. Nonorthogonal parameter-coordinate changes require an
explicit corresponding metric; duplication still changes weights, never creates independent
measurements. Thus it repairs precisely projective-scale dependence, not every experimental-
design issue.

The three Lean declarations compiled successfully with only propext, Classical.choice,
Quot.sound. Frozen SHA256: 44857d44fcbf0669a047a256792f4941f7568f9bf36becbbd977e133b29a815a.
The sixth homogeneous equation is redundant for this particular impossibility certificate;
the compiler's unused h5 warning does not drop any claimed hypothesis or permit a false result.
The first attempted shell write used a wrong relative path and wrote no Lean file; the
successful absolute-path run is the compiled artifact. No approved or original file changed.
