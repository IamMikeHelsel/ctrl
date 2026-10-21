# M05 independent critique

AI-written by the independent critic; inherited root model, exact runtime identifier unavailable.
This is an audit of the proposed reduction and exact rational calculations. It does not resolve
MF13, establish novelty, or certify a physical system. Original research notes were not edited.

## Verdict

**GO for a rank-aware compatibility and norm-bound gate. NO-GO for treating three moments or
involution-generated pairs as universally sufficient.** The generic reduction remains useful.
Its stated extension to exceptional spectra is false, with small exact full-rank witnesses.
The existing prototype already checks the full reduced residual; this audit found a written
claim failure, not evidence that that prototype accepts the exact bad pair.

## Exact independent checks

`critic_exact.py` uses standard-library Fraction arithmetic and its own matrix/rank code.
`critic_exact_results.json` records:

| Pair/type | rank Phi | augmented rank | cokernel | H-kernel | span of three W |
|---|---:|---:|---:|---:|---:|
| K=Y=diag(J,2J,3J) | 12 | 12 | 3 | 9 | 3 |
| K=diag(J,2J,3J), Y=diag(2J,J,3J) | 8 | 9 | 7 | 13 | 2 |
| K=diag(J,2J,J/2), Y=diag(J,J/2,2J) | 0 | 1 | 15 | 21 | 1 |
| Nonsemisimple paired Jordan3 example | 12 | 13 | 3 | 9 | 3 |

For the swapped pair, T=YK=diag(-2I4,-9I2), RHS=diag(3J,-6J,0).
Every power moment vanishes: the first two block discrepancies cancel at the same eigenvalue.
Yet W=diag(J,0,0) annihilates Phi and has Frobenius pairing 6 with RHS.
No compatible A exists. Both K,Y are invertible with squared Frobenius norm 28.
Common scaling by 1/sqrt(28) preserves both paired equations and their inconsistency;
using rational unnormalized matrices is not a loophole in the normalized claim.

The same pair is Y=QKQ with symmetric orthogonal Q exchanging the first two coordinate
planes. Thus the claimed universally compatible involutive Track B is also false.
The scalar-product pair makes this especially transparent: T=-I, Phi=0 and RHS nonzero.

I inspected and independently reran the inventor's exact checker, redirecting its output to
`critic_inventor_replay.json`. I inspected the domain checker's matrix/basis construction,
RREF, full cokernel and Frobenius adjoint tests, then reran four cases including the rational
Householder pair; `critic_domain_replay.json` binds the consulted source hash. The domain
checker runs all 315 basis adjoint identities per pair. I also reran the inventor's 666
quadratic-coefficient tests for its Hilbert-Schmidt norm identity; output is
`critic_norm_replay.json`. These are exact Python computations, not kernel proofs.

## Algebra and generic scope

With T=YK, T^T=KY and **T^T K=KT**. The form is K, not K^-1. An off-block rational Y in
my checker satisfies the K identity and violates the claimed K^-1 identity.
For Phi(H)=T^T H-H T on symmetric H, the Frobenius adjoint is

    Phi*(W)=T W-W T^T  (W skew).

The three witnesses are W_j=T^j K^-1, j=0,1,2. Their correct pairing is

    <W_j,RHS>_F = -tr(W_j RHS) = tr(T^j(Y²-K²)).

One displayed formula in the original note has the opposite sign; vanishing tests are
unchanged. All witness annihilation and pairing signs were checked exactly on the fixtures.
The full cokernel is W=ZK^-1 with [T,Z]=0 and Z^T K=KZ. Polynomial Z are only a subset
in general; higher scalar moments cannot detect the swapped example's hidden discrepancies.

The generic claim has a sound hand argument after correcting the form. The skew pencil
Y-tK^-1 shows the characteristic polynomial is a square via the Pfaffian determinant.
For three distinct reduced roots, the complex generalized eigenspaces are symplectic
2-planes. A symplectically selfadjoint map on such a plane is scalar, giving semisimplicity.
The symmetric kernel has three arbitrary symmetric 2x2 diagonal blocks (dimension 9);
Phi therefore has rank 12. The three W are independent by a Vandermonde argument, so the
three moments suffice on that stratum. This is an independent hand derivation, not a Lean proof.

For semisimple eigenspaces of dimensions 2m_i, cokernel dimension is
sum_i m_i(2m_i-1), giving ranks 12,8,0 for patterns (1,1,1),(2,1),(3).
Repeated roots alone do not imply rank drop: the explicit paired Jordan3 example has rank12.
A discriminant test is a conservative chart alert, not a complete compatibility classifier.
The canonical stabilizer SO(2)^3 also assumes distinct K weights; equal weights enlarge it
(e.g. U(3)). Setting three selected Y entries to zero has not been proved a global gauge slice.

I checked the rank-at-most-four same-square hand argument: signed 2x2 SVD can use two SO(2)
rotations, with signs retained in the diagonal singular factors; this preserves J and permits
the reflection cancellation. Coupling to the orthogonal complement preserves energy because
S²=-K². No defect was found in that hand derivation, but this audit did not formalize it or
verify that it is new. The rank-six same-square extension remains unsupported.

## Stronger actionable bound

For unit x and symmetric rank-one X=xx^T,

    ||L_A(X)||F² = 2||Ax||² + 2(x^T A x)².

Consequently s²>=2||A||op². Since H is symmetric and Y is skew,

    ||AK||F² = ||H+Y/2||F² = ||H||F² + ||Y||F²/4.

For a compatible equal-norm pair with q=||K||F²=||Y||F²>0, these imply

    s² >= 1/2 + 2||H||F²/q.

For any skew test W with Phi*W nonzero, Cauchy-Schwarz gives

    ||H||F² >= <W,RHS>F² / ||Phi*W||F².

If Phi*W=0 and the numerator is nonzero, the pair is inconsistent instead.
Thus the lower bound is an exact certificate valid over **all** nullspace choices of H.
No optimization convergence assumption is needed.

`critic_gate.py` computes Phi*W directly, independently of the inventor's basis projection,
reproduces the rational involution path bounds, and checks each pair's full consistency.
For t=1/4 it proves

    s² >= 139344560041 / 121419488960 > 1.

The t=1/8,1/16,1/32,1/64 fixtures also exclude s<1. The t=1/2 bound is less than one and
is honestly inconclusive. These finite fixtures are not a proved interval in t.
Since the paired skew value is 1 but may not be the top skew singular value, this excludes
s<1 at those pairs; it does **not** exclude every possible MF13 violation among their A.
The gate is appropriate when searching normalized top-skew pairs, or when trying to obtain
the sufficient certificate s<1 from a fixed pair.

## Repaired next gate and limits

Build the entire rational 15x21 Phi, compute rank and augmented rank, and retain exactly
21-rank variables only after compatibility passes. Alternatively supply a full cokernel
annihilation certificate. Moments remain cheap diagnostics. A three-moment shortcut requires
proved rank12 and witness independence, not an empirical singular-value threshold.
Then apply the exact W norm bound before expensive inner optimization. A conic dual witness
must annihilate every affine direction and have certified nuclear norm at most one; numerical
stationarity or BFGS success is insufficient.

The original `test_general_compatible.py` computes the full reduced residual and rejects
values above 1e-8. It does not hard-code nine nullspace vectors, although its documentation
suggests nine. Its finite differences, SVD tolerance, BFGS and Nelder-Mead results remain
numerical diagnostics. A value below one needs an exact compatible reconstruction plus a
validated spectral upper bound. Global coverage and arbitrarily small boundary gaps are open.

Next bounded test: derive a symbolic interval certificate for the near-degenerate path's
adjoint bound, include compatible repeated-root positive controls, and formalize the bound's
norm/adjoint bridge. Do not spend another batch merely projecting moments near a singular chart.

Quality of this audit: 18/20 (90%; exact reproducibility and discriminatory value strong;
generic/analytic arguments and current gate not Lean checked). Subjective confidence in the
finite incompatibility conclusions: >99%; this is not a calibrated scientific-success estimate.


## Independent minimum-norm certificate follow-up

The inventor then supplied all six full minimum-Frobenius-norm certificates in
`inventor_minnorm.json`. My separate `critic_verify_minnorm.py` imports no producer code.
It reconstructs K,Y,Phi,RHS and the diagonal Frobenius Gram matrix G from the declared path;
checks the selected rows span Phi; verifies all 15 primal equations; verifies
Gh=M_J^T z; and checks h^T G h=b_J^T z. Both original equations for the reconstructed A
also pass. Source hashes and exact verified values are in `critic_minnorm_results.json`.

Why this proves the minimum: any feasible h+d has M_J d=0, hence
h^T G d=z^T M_J d=0. Its energy is h^T G h+d^T G d, at least the reported value because
G has positive diagonal entries 1 or 2. This is a certificate proof, not trust in a solver.

All six certificates passed. Altering one H coefficient, one RHS entry, or one dual entry
in every certificate produced 18 independent rejections. At t=1/4 the strengthened bound is

    s² >= 1215515810338397 / 299535322677248 > 4.

The t=1/2 bound remains below one and inconclusive. The same top-skew normalization caveat
applies. The verifier uses explicit exceptions, not Python assertions, for acceptance.
Scoped ruff checks pass; these artifacts are a Python exact-certificate consumer, not Lean.

## The remaining t=1/2 fixture is excluded by full-nullspace testers

The H-only gate was inconclusive at t=1/2. The inventor supplied stronger fixed symmetric
input certificates, and `critic_verify_testers.py` independently consumed them without any
producer imports. It verifies the complete nine-dimensional kernel span, reconstructs
A0 and every affine direction from the original pair, reconstructs the weighted test Gram
matrix and linear term, checks exact normal-equation stationarity, and checks the reported
minimizer and both original paired equations. All 13 universal test/aggregate certificates
pass; nine kernel/optimizer/bound mutations across the I, Q and Hilbert-Schmidt cases fail.
The six single-coordinate rank-one testers yield zero lower bounds, correctly retained as
inconclusive rather than combined into a false guarantee.

For the fixed t=1/2 pair, the full-affine minimum of ||L_A(I)||F²/||I||F² is

    8193163298903 / 5845607424000 > 1,

and the Q test gives 3483573947231/1848445440000 > 1. Thus every compatible A at this
fixed pair has s>1. Together with the H gate, all six tested nonzero path parameters are
excluded from the sufficient s<1 search. No continuous interval or entire involutive family
is excluded by these finite certificates.

The normal Gram matrix is positive semidefinite by its explicit sum-of-squared-output
construction with positive weights. Exact stationarity therefore proves the global
minimum over the full affine space: any displacement adds a nonnegative quadratic form.
Dividing by the positive weighted sum of input squared norms gives a valid lower bound
on s². This is a quadratic certificate, not an optimizer-status assertion.

The semantic boundary remains essential: the fixed coupled skew value is 1 and need not
be maximal. Showing s>1 does not imply s>=k for that A. The certificates exclude these
pairs from a normalized-top-skew counterexample route; they are not MF13 proofs.

## Independent Lean witness and conditional structural reduction

I independently compiled root's `RepeatedSpectrum.lean` with the repository's pinned
Lean 4.33.1 using `lake env lean`. Exit status was zero. `critic-lean.log` records all five
printed theorem closures with only propext, Classical.choice and Quot.sound. Reviewed source
SHA256: `157614c2870f7da98ac22c9109442be8574f75fb97d4af797ef1a282f50a497c`.
The theorems check KY=YK=-I, skewness/equal squared-energy traces, no coupled solution,
zero reduced map for every H, and zero moments for every natural exponent. They are exact
statements about the displayed unnormalized matrices. Invertibility and the normalized
counterexample interpretation follow by elementary algebra, but a unit-Frobenius
normalization theorem was not included in this file. This is kernel evidence for a bad
search parametrization, not for failure of the original norm conjecture.

The domain worker's involution symmetrization also checks by hand. For Y=QKQ and symmetric
orthogonal Q, R(A)=Q A^T Q preserves both coupled equations. Orthogonal conjugation identifies
L_R(A) with the adjoint of L_A, preserving restricted norms. Thus B=(A+R(A))/2 has s(B)<=s(A),
preserves the pair, and C=QB is symmetric. Moreover conjugating the output of L_B by Q gives
the self-adjoint map X -> C X Q + Q X C. This is a valid search reduction for normalized
coupled pairs; it does not assert all symmetric coefficient pairs have domination.

I independently inspected Proposition 9 in the author-hosted
[Kalantarova–Tuncel paper](https://www.math.uwaterloo.ca/~ltuncel/publications/1805.09737.pdf).
It gives interlacing for a symmetric tridiagonal coefficient paired with a diagonal one.
For Q with one exceptional-sign eigenvector, orthogonally tridiagonalizing C while fixing
that vector leaves Q diagonal. Applying the proposition to the displayed self-adjoint map
therefore excludes signatures (1,5) and (5,1) from the normalized s<1 route. Scalar Q is
also excluded. The reduction and tridiagonalization argument are hand mathematics using a
published theorem, not a new Lean result or a novelty claim. Signatures (2,4) and (3,3)
are not covered. The tested path has signature (4,2), so its finite certificates remain useful.

A separate negative Lean control changes the claimed all-moment value from zero to one
while retaining its proof. `critic_false_moment.lean` is deliberately false and must not be
imported into any accepted project. Compilation exits 1, with the intended base-case and
successor type mismatches; its failed declaration also prints sorryAx, which is rejected.
The rejected log is `critic-negative-lean.log`. An initial wrong-working-directory attempt
was only a setup failure and is preserved as `critic-negative-setup-failure.log`; it is not
counted as a successful negative control. The original accepted source remains unchanged.
