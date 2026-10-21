# M05 inventor: compatibility, hidden modes and bounded search

AI-written; inherited root model, exact runtime identifier unavailable. Source inspected: frozen M05 card and `work/pod/mf13/theory/REDUCED_SEARCH.md`. No historical MF13 file modified. This is exact rational computation and algebraic derivation, not Lean certification or a resolution of the norm conjecture.

The question remains whether the Frobenius operator norm of L_A(X)=AX+XA^T on Sym(6) dominates that on Skew(6). A failure of the proposed singular-pair parametrization is not a counterexample to that question.

## Four materially different bridges

1. **Adjoint/Fredholm certificates, as in constrained mechanics.** Map the paired singular equations to Phi(H)=RHS, with H symmetric and A=(H+Y/2)K^-1. A self-stress W in the adjoint kernel annihilates every permitted H; a nonzero pairing with RHS certifies incompatibility. Assumes invertible skew K and exact linear algebra. Cheap falsifier: a rank-increasing augmented matrix despite vanishing scalar moments. This succeeds below. Mechanically, a load can balance total force yet violate a hidden constraint; no mechanics theorem is imported.

2. **Critical camera configurations and spectral strata.** A minimal pose solver relies on isolated roots and a valid rank/elimination chart; the proposed three-moment solver similarly relies on a generic rank-12 Phi chart. Repeated roots of the cubic square root of charpoly(YK) mark candidate chart failures. A discriminant is an alert, not by itself a complete test: compute the full exact adjoint basis/rank when the chart fails. Assumes only algebraic matrices; diagonalizability or a fixed kernel dimension must not be silently inherited. Cheap falsifier: repeated-root examples with both compatible and incompatible RHS. Below, ranks 0 and 8 occur, versus generic rank12. Jordan blocks remain a separate future test.

3. **Unexpected bridge: moment tomography and unobservable hidden modes.** The moments trace((YK)^j(Y²-K²)) inspect only block-total discrepancies when eigenvalues collide. Opposite discrepancies inside one repeated eigenspace cancel in every power moment, just as a single aggregate sensor cannot distinguish opposite hidden-state errors. Map powers of YK to observable channels and additional cokernel vectors to missing sensors. Assumes nothing about a physical sensor: this is a precise linear-algebra analogy. Cheap falsifier: swap two skew block amplitudes. All moments vanish while a local block witness detects residual6. Higher scalar moments cannot repair this particular failure.

4. **Port-Hamiltonian structure plus conic dual bounds.** H is a symmetric compatibility variable and K supplies an invertible skew structure, resembling energy/interconnection coordinates. Here H is not assumed positive, A need not be passive, and no stability follows. Use the structure to parameterize compatible A, then use a convex norm-dual witness Z with nuclear norm <=1 and <Z,B_r>=0 for all inner affine directions to certify min_z ||B_0+sum z_r B_r|| >= <Z,B_0>. Cheap falsifier: check every annihilation and norm condition exactly; a merely stationary numerical BFGS point is insufficient. A simpler norm gate below already rules out portions of a near-degenerate compatible path.

## Fresh exact tests

`inventor_exact.py` builds the 15-by-21 rational Phi matrix and checks a concrete Frobenius adjoint witness against all21 symmetric basis columns.

Let J=[[0,1],[-1,0]], K=diag(J,2J,3J), Y=diag(2J,J,3J). Both are invertible and have equal squared Frobenius norm28. Common normalization by sqrt28 preserves the paired-equation question.

- YK=diag(-2I2,-2I2,-9I2).
- All three trace moments vanish; indeed every power moment vanishes.
- RHS=diag(3J,-6J,0).
- rank(Phi)=8, rank([Phi|RHS])=9; symmetric kernel dimension13, skew cokernel dimension7.
- W=diag(J,0,0) annihilates all21 columns and has <W,RHS>_F=6.
- Hence no A solves both paired equations for this pair.

Positive controls: Y=K with amplitudes1,2,3 has rank12 and consistent RHS0. K=Y=diag(J,J,J) has rank0 and consistent RHS0. Therefore degeneracy must not mean automatic rejection of the entire stratum.

## A compatible path approaching the incompatible pair

`inventor_perturb.py` sets Q0 to swap coordinate planes(0,1) and(2,3), fixing(4,5). Let U(t) rotate coordinates0,4 with rational cosine(1-t²)/(1+t²) and sine2t/(1+t²). Define Q(t)=U(t)Q0U(t)^T and Y(t)=Q(t)KQ(t).

At each tested t=1/2,1/4,1/8,1/16,1/32,1/64:

- Q²=I exactly; all three moments vanish exactly.
- rank(Phi)=rank(augmented)=12.
- An exact particular H reconstructs an A satisfying BOTH original paired equations, not merely the reduced equation.
- The fixed former cokernel witness yields ||H||_F >= |<W,RHS>|/||Phi*W||_F. Exact rational squared lower bounds are saved; approximate norm bounds are1.865,3.011,5.094,9.615,18.929,37.705 respectively.

At t=0 the pair is inconsistent. The diverging bound is structurally expected: a bounded sequence of exact compatible A approaching this pair would have a convergent subsequence, and continuity would yield an impossible limiting solution. This argument establishes divergence for any such sequence; the finite tests alone do not establish a complete symbolic description of this path.

## Bound the target search instead of chasing infinity

For n=6, fresh algebra gives

    ||L_A|Sym||_HS² = 8||A||_F² + (tr A)².

`inventor_norm_gate.py` checks all666 coefficients of this quadratic identity using rational unnormalized orthogonal symmetric bases. Thus s(A)>=sqrt(8/21)||A||_F. A counterexample normalized to skew singular value1 and s(A)<1 must have ||A||_F<sqrt(21/8).

On the displayed path, ||K||op=3 and ||Y||F/2=sqrt7<3. Since H=AK-Y/2, ||H||F<=3||A||F+sqrt7. Any exact lower bound ||H||F>9 therefore forces ||A||F>2 and s(A)>sqrt(32/21)>1. The tested t=1/16,1/32,1/64 points satisfy this exclusion. This rules out a strict symmetric norm below the paired singular value1 at those pairs; it does not say their top skew norm is1 or solve the general conjecture.

## Next small test and boundaries

GO for a bounded search gate: normalize a candidate top skew singular pair to value1; first certify full Phi compatibility, then reject any pair whose exact adjoint residual bound forces ||A||F>=sqrt(21/8). Only then run the convex inner search. Do not hard-code nine nullspace coordinates on exceptional strata.

Next test: derive the full symbolic rank/discriminant partition for this rational path and prove an interval t near0 is excluded by the norm gate, retaining compatible repeated-root cases. Independently verify the Hilbert-Schmidt identity and all adjoint weights before formal promotion. Other routes remain candidates; no primary literature novelty review was performed in this role.

## Sharper PM/critic gate, independently derived

Root and critic suggested replacing the Hilbert-Schmidt estimate with a rank-one symmetric test. For any unit x, S=xx^T has Frobenius norm1. Writing u=Ax gives

    ||L_A(S)||F² = ||ux^T+xu^T||F² = 2||u||²+2(x^T u)².

Taking the maximizing x gives s(A)²>=2||A||op². Since H is symmetric and Y skew, <H,Y>F=0 and AK=H+Y/2 yields ||AK||F²=||H||F²+||Y||F²/4. The product inequality ||AK||F<=||A||op||K||F therefore gives, for equal squared norms q,

    s(A)² >= 1/2 + 2||H||F²/q.

Here q=28, so any adjoint-derived lower bound l on ||H||F² gives s(A)²>=1/2+l/14. These inequalities apply to EVERY compatible H, including all nullspace choices, and need no SDP solve.

Exact regenerated values appear in `inventor_sharp_gate.json`, produced by `inventor_norm_gate.py` after the perturbation script:

| t | exact lower bound on s(A)² | approximate | excludes s(A)<1 |
|---|---|---:|---|
| 1/2 | 10321201/13790000 | 0.748455 | no |
| 1/4 | 139344560041/121419488960 | 1.147629 | yes |
| 1/8 | 3981021109620361/1691446396640000 | 2.353619 | yes |
| 1/16 | 188920304730664417801/26593574892799093760 | 7.103983 | yes |
| 1/32 | 11252158704696859428186121/431222427122782400000000 | 26.093631 | yes |
| 1/64 | 719131696001763863790049533961/7046868544882336353974927360 | 102.049824 | yes |

This improves the tested exclusion cutoff from t=1/16 to t=1/4. No assertion is made about every intermediate t without a symbolic/interval proof. Equality q=28 and common normalization are explicit; this is not a bound comparing s(A) to a possibly larger top skew singular value.

## Best adjoint certificate for the Frobenius H bound

The PM requested optimizing the dual witness rather than retaining a convenient W. `inventor_minnorm.py` constructs the exact Gram G=diag(1 on Eii,2 on Eij+Eji), picks12 independent rows M_J, and solves

    (M_J G^-1 M_J^T) z = b_J,
    h = G^-1 M_J^T z.

It verifies all15 original reduced equations and reconstructs A to check both original pair equations. The serialized certificate records M,b,G,J,z,h and exact equality h^T G h=b_J^T z. For any other feasible h+d, M_J d=0, hence h^T G d=z^T M_J d=0. Thus its objective is h^T G h+d^T G d, proving global minimality with no numerical optimization assumption.

At t=1/2 the exact minimum is ||H||F²=72757073677/15973110784, giving s(A)²>=184568849165/223623550976≈0.825355. This strengthens0.748455 but remains below1: the gate must report **inconclusive**, not discard this pair.

For t=1/4,1/8,1/16,1/32,1/64, minimum H norms are approximately7.05777,26.9459,105.779,420.664,1680.06. The resulting s² lower bounds are4.05800,52.3630,799.725,12640.35,201614.70. These are exact rational certificates with decimal summaries. Observed growth is consistent with 1/t² in H norm, but this finite sequence is not an asymptotic theorem.

The transferable result is an inexpensive linear solve supplying the best Frobenius-H dual gate before a harder operator-norm optimization. Failure of this gate, as at t=1/2, leaves the convex norm problem genuinely open for the pair.

## Fixed symmetric testers close the t=1/2 gate gap

The preceding Frobenius-H gate's failure led to a different exact test, not a claim of a promising counterexample. `inventor_testers.py` forms a complete9-dimensional nullspace basis of the exact15-by21 compatibility matrix and verifies every basis vector against all15 rows. Write A(z)=A0+sum z_i A_i.

For a fixed symmetric test matrix S, the nonnegative quadratic objective ||L_A(z)(S)||F² has normal equations Gz=-ell. The script solves these rationally and verifies exact stationarity. Since G is an actual Gram matrix, a stationary point is a global minimum even when G is singular. Original pair equations are checked again at each minimizing A. The output includes tests, weights, Gram matrix, linear vector, optimizer, minimum objective, denominator, A and the full kernel certificate.

At t=1/2:

- S=Q, where Q is the generating symmetric orthogonal involution: **for every compatible A**, s(A)²>=3483573947231/1848445440000≈1.884596576.
- S=I: **for every compatible A**, s(A)²>=8193163298903/5845607424000≈1.401593146.
- The full orthonormal symmetric-basis aggregate also gives the universal bound1.241655186.

Thus all six sampled nonzero path pairs are now excluded from achieving s(A)<1, with the first pair excluded by a distinct objective-aware quadratic certificate. This does not prove exclusion of the continuous path or every pair generated by an involution.

The distinction between testing one A and all A is concrete: min-H A0 has ||L_A0(e0 e0^T)||²≈4.73373, but each individual coordinate rank-one test has universal minimum0 when the compatible nullspace is reoptimized. A particular-matrix failure cannot substitute for the Q or I universal lower bound. Different coordinate tests can have different minimizers.

The reusable mechanism is a cheap exact quadratic rejection gate before convex spectral-norm minimization: choose one or several fixed symmetric testers; minimize their weighted output energy over the full compatible affine space; divide by their total weighted input energy. Any result>=1 rejects that pair's strict counterexample route. A result<1 remains inconclusive. No optimizer termination assumption or floating PSD tolerance is used here.
