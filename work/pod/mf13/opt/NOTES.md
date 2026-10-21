# MF-13, dimension 6: optimization search

Numerical search only. Nothing here is a proof that the symmetric-maximizer conjecture holds for every real 6×6 matrix, and nothing here is a counterexample.

## Problem

For \(A\in\mathbb{R}^{n\times n}\) the Lyapunov operator is
\[
\mathcal L_A(X)=AX+XA^\top.
\]
The Frobenius-induced operator norm splits over the orthogonal invariant subspaces of symmetric matrices \(\mathbb S_n\) and skew-symmetric matrices \(\mathbb K_n\):
\[
s(A)=\|\mathcal L_A|_{\mathbb S_n}\|,\qquad
k(A)=\|\mathcal L_A|_{\mathbb K_n}\|.
\]
Both are largest singular values of \(\mathcal L_A\) in an orthonormal basis of the subspace (diagonal matrices \(E_{ii}\), and \((E_{ij}\pm E_{ji})/\sqrt2\)). Equivalently, in the integer basis used by Kressner–Vandereycken, the squared norms are generalized eigenvalues of \(B^\top DB\) against the Gram matrix \(D\).

The Byers–Nash / symmetric-maximizer conjecture says \(k(A)\le s(A)\) for every real \(A\). Chen and Tian (2015) proved it for \(n\le 5\). Kressner and Vandereycken (arXiv:2608.20875v1, August 2026) disproved it for every \(n\ge 7\) by an integer 7×7 matrix and a direct-sum padding. Their paper states that \(n=6\) is open. It does not report a dimension-6 search. Section 4 describes a large equality ridge \(k(A)=s(A)\) on the Frobenius sphere, which Adam can leave in dimensions where counterexamples exist.

Their Theorem 2 matrix and skew witness were reproduced here. Float64 singular values satisfy
\[
s(A_7)^2=1195.593984837754,\qquad k(A_7)^2=1196.025223697914,
\]
matching the paper’s displayed approximations 1195.593985 and 1196.025224. On the unit sphere that gap is relative \(1.80\times 10^{-4}\). The same code, run as Adam on the 7×7 sphere, finds many fatter counterexamples. The best in a short run has
\[
s=0.8051468103934099,\quad k=0.8109423819999578,\quad (k-s)/k=0.007146711943029608.
\]
Its top skew witness is rank 6, with singular values
\[
(0.57836,\,0.57836,\,0.35872,\,0.35872,\,0.19188,\,0.19188,\,0).
\]
The final 0 is forced by odd dimension. Saved at `results/smoke_gap7/best_A.npy`.

## What a dimension-6 counterexample must look like

Skew matrices have even rank. The research notes’ same-square argument says a skew witness of rank at most 4 has a symmetric matrix of the same Frobenius norm whose Lyapunov image is at least as large. A strict counterexample in dimension 6 therefore needs an invertible skew singular pair \((K,Y)\):
\[
AK+KA^\top=Y,\qquad A^\top Y+YA=K
\]
after scaling so that this singular value equals 1, and then \(s(A)<1\). The forward elimination in those notes is linear in the symmetric part of \(AK\). Numerically, for generic invertible pairs the coupled system in the 36 entries of \(A\) has rank 27 and nullity 9, and the three scalar conditions
\[
\operatorname{tr}((YK)^j(Y^2-K^2))=0,\qquad j=0,1,2,
\]
cut out the consistent pairs. On every Newton success in this search, those three conditions also killed the linear residual and the higher moments. The calibration pair \(K=Y=\operatorname{diag}(J,2J,3J)\) has exact optimum \(s=1\), attained at \(A=I/2\), and the SDP/L-BFGS solver returns \(1\) to \(10^{-15}\) with a zero subgradient certificate. The equal-weight complex structure \(K=Y\propto\operatorname{diag}(J,J,J)\) likewise has minimum \(s=1\).

So the search quantity is
\[
\phi(K,Y)=\min\bigl\{s(A):A\text{ satisfies the coupled equations for }(K,Y)\bigr\}.
\]
The inner problem is convex (spectral norm of an affine matrix family). A value \(\phi<1\), or any matrix in the family with \(k>s\), is a counterexample candidate. L-BFGS on that convex problem matched Clarabel’s SDP to about \(10^{-7}\) on test pairs.

## What was run

All code is in this directory. Operator-norm gradients were checked by central differences (max error \(4\times 10^{-9}\)). The coupled system round-trips a true singular pair to residual \(10^{-15}\).

1. **Unit-sphere Adam, dimension 6, no barrier.** Same JAX Adam that finds a relative gap \(+7\times 10^{-3}\) on \(n=7\) within a fraction of a second. 18857 random starts, 1800 seconds, seed 11 (`results/long/gap0b`). Best gap
   \[
   k-s=-1.5258427854547563\times 10^{-9},\qquad (k-s)/k=-1.6913025079534563\times 10^{-9}.
   \]
   The witness singular values are
   \[
   (0.61695,\,0.61695,\,0.34551,\,0.34551,\,6.84\times 10^{-5},\,6.84\times 10^{-5}).
   \]
   This is the rank-4 equality ridge. Unconstrained maximization of \(k-s\) falls onto it and stops with a gap at rounding level, from below.

2. **Exact bilevel search on full-rank pairs.** Canonical skew \(K=\operatorname{diag}(aJ,bJ,cJ)\) with \(a,b,c>0\), Newton retraction of \(Y\) onto the three moment conditions, then convex minimization of \(s\) over the 9-dimensional affine family. A penalty Adam stage (large \(\rho\) on \(\|A^\top Y+YA-K\|_F^2\), log-det barrier) produced a feasible pair with singular values about \(0.48,0.37,0.36\) and \(\phi=1.00007744\). Clarabel agreed. Finite-difference L-BFGS on the 18-parameter retraction, plus perturbations and fresh starts (`results/long/polish`), drove that pair to
   \[
   \phi=1.000000020653004.
   \]
   A line search along the symmetric-norm gradient and 30 random steps of size \(10^{-4}\) do not decrease \(s\). The top symmetric singular value is simple but the next one sits \(8.6\times 10^{-8}\) below it, so the \(2\times 10^{-6}\) raw gradient is the nonsmooth cluster, not a useful descent direction. mpmath at 40 decimal places on this float64 matrix gives
   \[
   \begin{aligned}
   s&=1.000000020653004191583823673363799253467,\\
   k&=1.000000000000000232216786656179737688484,\\
   k-s&=-2.065300395936703701718406156498260216759\times 10^{-8}.
   \end{aligned}
   \]
   Coupled residual \(8.4\times 10^{-12}\). Both witnesses are well conditioned (smallest singular value \(0.360\)). Matrices: `results/best_fullrank_A.npy`, `best_fullrank_K.npy`, `best_fullrank_Y.npy`, and `results/best_candidate.json`. Other polished basins stayed higher: \(\phi\in\{1.000017,\,1.00004,\,1.00013,\,1.0028,\,1.05,\,1.13,\,1.20\}\), the last of these with a witness singular value \(0.006\) (the ridge side).

3. **Random feasible pairs before outer optimization.** Thirty-five consistent samples gave minimum \(\phi=1.00075\), on a boundary pair with smallest singular value \(0.004\). Certified interior samples (simple top singular value, subgradient \(<10^{-7}\)) had \(\phi\ge 1.37\). No sample had \(\phi<1\).

4. **Deflation from dimension 7.** Parameter pack \((B,u,v,w)\) on the unit sphere in the splitting
   \[
   A(t)=\begin{pmatrix} B & t u\\ t v^\top & t w\end{pmatrix},
   \]
   so \(t\to 0\) really deletes the last coordinate (an earlier run without the sphere constraint let \(u,v\) grow like \(1/t\) and never decoupled). Reoptimizing the published integer matrix along each deleted coordinate: the 7×7 relative gap stays positive down to about \(t=0.55\) for the most persistent coordinate and is negative by \(t=0.4\). The 6×6 block \(B\) has negative gap at every recorded \(t\), and at \(t=0\) Adam polishes it to a gap of size \(10^{-8}\)–\(10^{-10}\) (the ridge). The fat \(n=7\) example (relative gap \(0.00715\)) dies between \(t=0.7\) and \(t=0.55\); its best principal 6×6 submatrix has gap \(-0.00825\). Eight Grassmann compressions of the integer matrix, each polished by Adam in dimension 6, all finish with \(k\le s\). All seven principal 6×6 submatrices of the integer counterexample have negative gaps; the least negative is deletion of index 5, relative gap \(-0.00946\). A plain last-row scaling of the integer matrix, with no reoptimization, is already negative at scale \(0.9\).

5. **Equal-weight and calibration families.** Both have exact minimum \(s=1\) on their coupled affine families (40 random samples in the equal-weight family had maximum gap \(-0.107\)). These are interior equality cases: full-rank skew pairs can saturate \(k=s\) without lying on the rank-4 ridge. The polished pair above is of that kind. \(K\) is canonical with three comparable weights; \(Y\) is not a scalar multiple of \(K\) (\(\|K-Y\|_F=0.538\), \(\|K+Y\|_F=1.926\)).

## Best gap

No matrix with \(k>s\) was found in dimension 6.

| search | best \(k-s\) | witness |
| --- | --- | --- |
| 18857 sphere Adam starts | \(-1.53\times 10^{-9}\) | third pair \(6.8\times 10^{-5}\) (rank-4 ridge) |
| best full-rank coupled pair, convex inner solve, mpmath check | \(-2.065\times 10^{-8}\) | all singular values \(\ge 0.360\) |

The relative gap on that full-rank matrix is about \(-2.07\times 10^{-8}\), far smaller than the \(10^{-6}\) discovery threshold and far larger than the coupled-equation residual. There is no positive gap to rationalize. The float64 matrix and the 40-digit singular values are the certificate that this particular candidate lies on the conjecture’s side.

## How the maximizers are arranged

Unconstrained maximization of \(k-s\) on the unit sphere converges to the equality ridge. The top skew witness there has two singular-value pairs of size \(O(1)\) and a third pair at \(10^{-5}\) or smaller: numerically rank 4, which the same-square argument says cannot win. The measured gap on that ridge is zero within \(10^{-9}\).

Full-rank coupled pairs are a different set. Random ones have \(\phi\) well above 1. Optimization pushes \(\phi\) down to 1 and stops. The calibration family and the equal-weight complex structure meet \(\phi=1\) exactly, with invertible \(K\) and \(Y\). The best optimized non-aligned pair meets \(\phi=1\) up to \(2\times 10^{-8}\), with a flat top of the symmetric spectrum and no descent step. Dimension-7 counterexamples, including ones whose relative gap is forty times the integer example, lose that gap when one coordinate is scaled out, and the surviving 6×6 block sits on the same nonpositive ridge.

The numerical picture is that the maximum of \(k-s\) in dimension 6 is 0, attained both on the rank-4 ridge and on a full-rank equality set (at least the calibration family), and that the obstruction to a strict counterexample is this equality set rather than a failure to leave the ridge.
