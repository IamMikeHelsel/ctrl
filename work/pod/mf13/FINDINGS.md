# Lane MF-13 findings (Byers–Nash, n = 6)

## M1: exact reduction (theory, numerically re-validated by opt and bilevel)
A strict n = 6 counterexample (k(A) > s(A), restricted spectral norms of L_A on skew/symmetric)
needs full-rank skew witnesses K, Y. With K = diag(aJ, bJ, cJ), compatibility of (K, Y) is
exactly m_j = tr((YK)^j (Y² − K²)) = 0 for j = 0, 1, 2 (YK is self-adjoint for the symplectic form
x^T K^{-1} y, so its spectrum is doubled and its minimal polynomial has degree ≤ 3). The compatible
A form a 9-dimensional affine family, and min s(A) over it is convex: 11 outer parameters.
See `theory/REDUCED_SEARCH.md`.

## M2: why n = 7 works and n = 6 may not
On the 6-dim support of the K–V 7×7 witness, the projected 6×6 block satisfies the conjecture with
margin (s² = 1149.8 > k² = 1090.3). The 7th coordinate penalises symmetric comparators whose
square differs from −K²; in n = 6 that penalty is absent.

## M3: Lean (independently recompiled 2026-10-18, 23 s, standard axioms only)
`theory/SameSquareExclusion.lean`, 21 theorems: same-square energy identity (any n), 2×2 signed
SVD, unconditional rank-2 and rank-4 same-square exclusion in Fin 6 for witnesses
Q·skewWitness(a,b)·Qᵀ, and the converse of the coupled elimination. Gap: the normal-form lemma
(every rank ≤ 4 real skew 6×6 matrix is such a conjugate) is not formalized.

## M4: numerical evidence (opt: 18857 sphere starts + exact bilevel + n=7 deflation)
No counterexample. Max k − s found is 0 (to 1e-9), attained on two sets: the rank-4 ridge and a
full-rank equality set containing K = Y = diag(J, 2J, 3J) (φ = 1 exactly). Best full-rank near-miss
k − s = −2.07e-8 at 40 digits. The same code finds n = 7 counterexamples with relative gap +0.007
immediately (positive control). Fat n = 7 examples lose their gap when a coordinate is scaled out.
Assessment: a proof for n = 6 now looks more plausible than a counterexample.

## M5: bilevel search (exact reduction, CMA-ES; `bilevel/NOTES.md`)
Positive control: random-start bilevel reaches n = 7 counterexamples (s = 0.99555, k = 1,
mpmath-verified from the 49×49 operator, gap 4.45e-3; `bilevel/candidates/`). n = 6: min f =
1 to ~1e-15 in all Track A runs; fixed K with the n = 7 witness shape: 1.00000075. The minimum
set is a large full-rank ridge (σ_min(K) up to 0.4). Proof lead: if K and Y share a symmetric
orthogonal involution T anticommuting with both, then f ≥ 1 (dual certificate Z₁ = −Y). Every
minimiser found lies in that 8-dim locus, but the locus is not all at f = 1, and pairs without a
common T are not covered. Correction to the reduction note: skew value 1 need not be the top skew
value (f < 1 still implies k > s). Proof attempt: `proof/`.

## M6: prover results (dual certificates; `proof/NOTES.md`, `proof/PROOF_SKETCH.md`)
- **A-free reformulation (proved, all n).** ⟨U, L_A V⟩ = 2⟨A, UV⟩ for symmetric U, V and
  ⟨Y, L_A K⟩ = −2⟨A, YK⟩ for skew K, Y. By the bipolar theorem, Byers–Nash(n) ⇔ N(YK) ≤ ‖Y‖‖K‖ for
  all skew K, Y, where N is the gauge of conv{UV : U, V unit symmetric} (an SDP), and
  sup_A k/s = max N(YK) over unit skew pairs.
- **Settled cases at n = 6:** rank K ≤ 4 or rank Y ≤ 4 (Lean rank-4 theorem plus the adjoint), and
  pairs sharing an anticommuting symmetric involution T (YK = (YT)(TK)).
- **Dimension reduction (proved):** N depends only on the restriction to range K + range Y. So
  BN(6) ⇔ BN(7) on pairs with ker K = ker Y, and every 7×7 counterexample needs misaligned kernels.
- **The Chen–Tian same-square method cannot prove n = 6.** `proof/cert_ss_fail.json`: a rational 6×6 A
  whose top skew singular vector is full rank and for which every same-square comparator falls short
  (ratio ≤ 0.91703, exact LDLᵀ checks over all 27 components).
- **Stronger n = 7 counterexample.** A monotone majorize–minimize ascent on the SDP dual lifts the K–V
  margin 1.00018 to k/s ≈ 1.0077888 (numerical; most random starts converge to the same value).
  Exact certificate `proof/cert_n7.json`: integer 7×7 A with entries ≤ 200 and an integer skew K, giving
  **k/s > 1.007307**. Verified independently by `verify_n7_cert.py`, which recomputes the skew lower bound
  exactly and checks c·G − M ⪰ 0 on Sym₇ by exact Fraction LDL. That code shares nothing with the prover's script.
- **n = 6 numerics:** 54 ascent starts never exceed 1 − O(1e-11). The limits are rank-4 or full rank on
  the common-T locus, and transversal second-order decay is strictly positive in all sampled directions.
- **Precise remaining gap:** show N(YK) ≤ 1 for unit skew 6×6 K, Y that are both invertible and share no
  anticommuting involution. A heuristic (non-rigorous) atomic-gauge test suggests YK is then not a
  convex combination of settled-case atoms, so a proof needs genuinely full-rank UV terms.
