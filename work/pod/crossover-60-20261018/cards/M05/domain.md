# M05 domain research: full compatibility beats moment-only screening

AI-written by the domain role, inherited root model; exact runtime identifier unavailable.
Original question: symmetric versus skew Frobenius amplification for real 6-by-6 Lyapunov
operators. This session tests a reduction used to investigate that question; it does **not**
produce a counterexample to the norm conjecture.

## Result and scope

The three trace moments are not sufficient on all invertible skew pairs, even if all higher
moments vanish too. An explicit rational pair has equal nonzero Frobenius norms and no
compatible matrix A. This refutes a universal reading of the reduction's sufficiency claim.
It leaves a properly qualified generic theorem untouched. Existing inspected search code
checks a full linear-system residual after the moment projection, so this is not evidence
that the current code accepts this pair.

Let J = [[0,1],[-1,0]], K = diag(J,2J,J/2), Y = diag(J,J/2,2J). Then:

- K and Y are invertible; both Frobenius norm squares equal 21/2.
- YK = KY = -I, so Phi(H) = KYH-HYK = 0 for every symmetric H.
- Every moment tr((YK)^j (Y²-K²)) is zero, for every nonnegative integer j.
- R = K³ - (Y²K+KY²)/2 = diag(0,-15J/2,15J/8), which is nonzero.

Thus Phi(H)=R is impossible. Jointly multiplying K,Y by sqrt(2/21) makes both unit norm;
Phi scales quadratically, R cubically, and the obstruction persists. Rational inputs are
used in the exact script; this normalization is an elementary real-algebra argument.

A less extreme witness uses K=diag(J,2J,3J), Y=diag(2J,J,3J). Here YK has two distinct
roots, all moments still vanish, Phi has rank 8, and its augmented system has rank 9.
Its RHS is diag(3J,-6J,0). Norm squares are both 28; unit normalization preserves failure.

## Exact derivation and complete criterion

For invertible skew K and skew Y, the first coupled equation AK+KAᵀ=Y is equivalent to
H=AK-Y/2 being symmetric and A=(H+Y/2)K⁻¹. Substitution into AᵀY+YA=K gives exactly
Phi(H)=R above, reversibly. Therefore this is a compatibility test for the two coupled
singular-pair equations, not an additional relaxation.

Use the Frobenius pairing <U,V>=tr(UᵀV). For symmetric H and skew W,

    <KYH-HYK,W> = <H,YKW-WKY>.

The latter matrix is symmetric, so the adjoint really is

    Phi*(W) = YKW-WKY.

The finite-dimensional alternative gives the complete criterion, with no spectrum or
multiplicity assumption:

    Phi(H)=R has a symmetric solution
    iff <W,R>=0 for every skew W satisfying YKW=WKY.

An implementable version constructs the 15-by-21 rational matrix of Phi, computes a basis
of its entire left nullspace, and checks every pairing exactly. Equivalently, check equality
of coefficient and augmented ranks. Inconsistent pairs have an explicit dual obstruction W.
Consistent pairs have an affine solution space of dimension 21-rank(Phi); nine is generic,
not universal.

Writing T=YK and W=ZK⁻¹ makes the cokernel condition

    TZ=ZT and ZᵀK=KZ.

Thus the full cokernel is the K-self-adjoint centralizer, multiplied on the right by K⁻¹.
Polynomial Z=T^j supplies W_j=T^j K⁻¹. These give

    <W_j,R> = tr(T^j(Y²-K²)) = m_j.

The sign is positive for m_j with this definition. The inspected REDUCED_SEARCH.md instead
prints the opposite sign in its intermediate pairing formula; vanishing is unaffected.
For T=YK, the symplectic self-adjoint identity is TᵀK=KT: the form is K, not K⁻¹.
The latter form works for the reversed product KY. This order matters.

Polynomial tests cover the whole cokernel only when those witnesses span it. For the scalar
product example the polynomial span has dimension 1 while the full cokernel has dimension
15. For the two-root swapped example the dimensions are 2 and 7. At the distinct-root
calibration they are 3 and 3. Repeated eigenvalues alone do not determine the rank in a
nonsemisimple case; use the actual operator or centralizer, not just eigenvalue counts.

## Reproducible exact evidence

Run from the ctrl checkout:

    uv run python work/pod/crossover-60-20261018/cards/M05/domain_exact.py

The script uses standard-library Fraction arithmetic, Gaussian elimination and explicit
unnormalized symmetric/skew bases. It writes domain_exact_results.json. It also accepts
--output to let an independent reviewer preserve a separate output. Every case checks
all 21*15 basis pairings for the adjoint identity, constructs the entire cokernel, checks
all obstruction pairings, and compares their vanishing with augmented-rank consistency.
Six polynomial witness/moment identities are checked exactly for each case.

| Pair | rank Phi | augmented rank | cokernel dimension | first three moments |
| --- | ---: | ---: | ---: | --- |
| K=Y=diag(J,2J,3J) | 12 | 12 | 3 | 0,0,0 |
| K=diag(J,2J,3J), Y=diag(2J,3J,4J) | 12 | 13 | 3 | -30,240,-2400 |
| K=Y=diag(J,J,2J) | 8 | 8 | 7 | 0,0,0 |
| K=diag(J,2J,3J), Y=diag(2J,J,3J) | 8 | 9 | 7 | 0,0,0 |
| Scalar-product obstruction above | 0 | 1 | 15 | 0,0,0 |
| K=Y=diag(J,J,J) | 0 | 0 | 15 | 0,0,0 |
| K=diag(J,2J,3J), Y=QKQ, Q=I-2vvᵀ/91, v=(1,...,6) | 12 | 12 | 3 | 0,0,0 |

The Householder case checks a non-block-diagonal rational pair, reducing reliance on examples
where all matrices commute. These are finite exact computations supporting the hand derivation,
not a Lean theorem, exhaustive classification, or novelty assessment.

Scoped `uv run ruff check` passes for domain_exact.py. NumPy/SciPy are absent from the current
project environment; no package download was needed for these exact tests.

## Existing source and implementation audit

Sources read (unchanged):

- work/pod/mf13/theory/REDUCED_SEARCH.md: generic rank claim, three-moment iff language,
  fixed nine-variable inner problem, and an unfinished lower-bound paragraph.
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/research/mf13-next-step.txt:
  audited forward identities and explicit warning that three-moment sufficiency was not proved.
- work/pod/mf13/theory/test_general_compatible.py: solve_pair builds full Phi and returns
  a residual and detected rank. min_sym_norm_for_pair returns None when res_norm>1e-8.
- work/pod/mf13/opt/lyap.py: factor_family builds the full 30-by-36 coupled system,
  uses its SVD rank and left residual, and sets consistent only below a relative threshold.
  Its nullity follows computed rank rather than a forced nine-dimensional assumption.

The numerical gate behavior is established by source inspection here, not by executing the
old NumPy/SciPy code. The exact scalar obstruction has large residual and is not an example
of a delicate floating-point near-threshold failure. The hand-written mathematical scope
needs tightening; these observations do not establish an implementation acceptance bug.

## Next discriminating task

Retain the full-cokernel criterion as the acceptance gate, with exact rank and explicit dual
obstructions when using rational pairs. Add the two obstruction pairs as isolated regressions
before integrating any changes into the active MF13 lane. For the generic reduction, prove
that the three polynomial witnesses span the cokernel under an explicit checkable hypothesis,
and identify rank-changing strata before treating the nine-variable search as exhaustive.

Research-quality assessment is left to the PM and independent critic. Subjective confidence:
high in the explicit rational obstruction; no confidence claim about resolving MF13.

## Follow-up within this session: sharp norm gate and rank strata

The PM's stronger gate is independently derived as follows. For unit x and S=xxᵀ,

    ||L_A(S)||F² = 2||Ax||² + 2(xᵀAx)²,

so s(A)² >= 2||A||op². Symmetric H and skew Y are orthogonal, hence

    ||AK||F² = ||H||F² + q/4 <= ||A||op² q,
    s(A)² >= 1/2 + 2||H||F²/q,

where q=||K||F²=||Y||F²>0. Any skew W provides the exact lower bound
||H||F² >= <W,R>²/||Phi*(W)||F² when its denominator is positive. If the denominator is
zero and numerator nonzero, compatibility itself fails. If both vanish, this W gives no
bound. Thus an adjoint lower bound >=q/4 excludes s(A)<1 for every compatible A in the pair's
entire affine family. This is a pre-search exclusion, not a certificate that the paired
singular value 1 is the top skew singular value.

The independent `domain_norm_gate.py` reconstructs the inventor's rational path and verifies
the same six exact bounds. At t=1/4 the bound on s² is
139344560041/121419488960 > 1. It also excludes t=1/8,1/16,1/32,1/64; t=1/2 remains undecided
by this gate. No claim is made about a whole interval. The output serializes K,Y,W, q, both
pairings and the resulting bound, permitting direct exact replay.

For a diagonalizable T=YK=PDP⁻¹ with distinct scalar blocks of multiplicities d_a, set
H'=PᵀHP. Then

    Pᵀ Phi(H) P = DᵀH' - H'D.

Both congruences are invertible on their symmetric/skew spaces, so

    rank Phi = sum_(a<b) d_a*d_b,
    nullity Phi = sum_a d_a*(d_a+1)/2.

This covers noncommuting K,Y and nonorthogonal P. It preserves rank and compatibility, NOT
Frobenius norms. Complex diagonalization is also valid for rank counting because extending
real scalars to C preserves rank. A nondiagonalizable T needs its actual operator/centralizer,
not this formula. For multiplicities (2,2,2), (4,2), (6), ranks are 12,8,0. The isolated
`domain_rank_transport.py` checks three nonorthogonal rational shears; the first two examples
have changed and unequal K,Y norms, explicitly exposing why norm bounds cannot be transported
this way. No global genericity theorem is needed for the exact rank/cokernel acceptance test.

## Bounded primary-source novelty screen

Freshly inspected on this session's research date:

- [Kressner–Vandereycken, 2026](https://arxiv.org/html/2608.20875v1) gives the exact order-seven
  witness and direct-sum extension, leaving order six unresolved. Its computational section
  describes direct norm-gap search and exact subsequent validation. It does not present this
  paired-cokernel screening construction in the inspected text.
- [Chen–Tian, 2016](https://files.ele-math.com/articles/oam-10-35.pdf), introduction and
  Lemmas 2.1–2.2, provides related symmetric/skew reduction and equal-norm comparison machinery
  for the generalized operator. That is relevant prior art, not evidence of novelty here.
- The [2015 Chen–Tian DOI](https://doi.org/10.1137/140974031) retrieval failed; no claim of
  reading that full proof is made.

The exact adjoint alternative and norm inequalities are elementary linear algebra. This
bounded check supports describing our result as a useful local search correction and new
regression witnesses within this project. It does not establish publication novelty or
priority for the combination. A broader literature review would be required for that claim.

## Involution family: structural reduction, not universal exclusion

For Y=QKQ with Qᵀ=Q and Q²=I, the six successful finite-point exclusions do not establish
that the whole family is excluded. A useful exact reduction follows directly from both
coupled equations. Set

    B = (A + Q Aᵀ Q)/2.

Then L_(Q Aᵀ Q)(K)=Q L_A*(Y) Q=Y, and its adjoint maps Y back to K. Hence B preserves
both coupled equations. Moreover, with C_Q(X)=QXQ,

    L_(Q Aᵀ Q) = C_Q L_A* C_Q.

C_Q is orthogonal and preserves symmetric/skew spaces. Therefore s(B)<=s(A), while
B=Q Bᵀ Q, so C=QB is symmetric. Any strict counterexample arising from an involution pair
has a representative B=QC with C symmetric and no larger symmetric amplification.
Equivalently, C_Q L_B(X)=C X Q+Q X C is a self-adjoint Jordan–Kronecker operator with the
skew eigenvector K and eigenvalue 1. Its norm on symmetric matrices is the remaining issue.

There is a partial whole-family exclusion. Q=±I makes B symmetric. If Q has signature (1,5)
or (5,1), tridiagonalize C orthogonally starting from the unique exceptional-sign eigenvector
of Q. The other basis vectors remain in its orthogonal complement, so Q remains diagonal;
C and therefore B=QC become tridiagonal. The known tridiagonal symmetric-maximizer result
then excludes these signatures. Standard symmetric tridiagonalization can handle Lanczos
breakdown by continuing an orthonormal basis in the complement. This is a hand reduction
using an existing theorem, not a new Lean certificate.

For the actual inventor path Q has signature (4,2), so that argument does not apply. Up to
Q->-Q, the genuinely unresolved structural cases are signatures (2,4) and (3,3). A concrete
next search can fix one of these diagonal signature matrices and vary the 21 entries of C,
looking for skew/symmetric norm separation in B=QC. Finding none is not a proof.

Primary-source guardrail: [Kalantarova–Tuncel's author-hosted paper](https://www.math.uwaterloo.ca/~ltuncel/publications/1805.09737.pdf)
contains the tridiagonal/diagonal interlacing result in Proposition 9, but its Example 11 shows
that weak interlacing fails for general symmetric pairs in dimension four. Thus it would be
incorrect to promote the reduction above by asserting a universal symmetric-pair spectral
domination theorem. The special condition Q²=I must still do real mathematical work.

A further exact finite probe addresses the unresolved signatures rather than assuming their
exclusion. `domain_involution_probe.py` minimizes ||B||F² over the Q-self-adjoint compatible
family B=QC, using rational weighted normal equations in the 21 symmetric entries of C.
The dual stationarity identity and both original paired equations are checked. Eight cases
(two K spectra, two rational reflection conjugations, both signatures (2,4) and (3,3)) all
have exact minimum ||B||F²>3/2. Therefore the symmetric tester Q proves s(B)>=1 in those
cases. Results and exact fractions are in domain_involution_probe_results.json.

This finite test did not falsify the tempting general bound ||B||F²>=n/4, but no proof of
that bound was found. It remains a conjectured sufficient route; the card must not turn
these eight samples or the earlier six path points into a whole-family exclusion.
