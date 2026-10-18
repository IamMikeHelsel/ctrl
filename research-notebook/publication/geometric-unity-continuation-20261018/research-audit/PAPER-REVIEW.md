# Independent source and theorem-scope review

Reviewed `paper/main.tex`, 18 October 2026, after the first draft existed. This review covers the source-facing mathematics and claim boundaries; it is not an independent recompilation of every Lean module.

Decision: acceptable working-paper scope, subject to final artifact status matching the final manuscript.

## Findings

1. The invariant-map proposition is correctly typed over the real numbers. Clifford conjugation is explicitly conjugate-linear after complexification. The factor i in G_2 and its absence in G_1 are correct. The full volume square and star signs are correct for dimension 14 and signature (7,7). The first draft had a numerical typo in the square exponent: 14·13/2 is 91, while 14·15/2 is 105 for the adjoint. Both are odd, so the stated signs are unchanged. The source audit has been corrected.
2. The representation-theoretic bridge is sound as a hand proof: Spin elements are even and fix the volume by conjugation; the metric identifies each exterior power with its real dual. No irreducibility or exact multiplicity classification is needed. The paper properly states a lower bound and keeps the full group/tensor theorem outside the Lean claims.
3. The paper distinguishes K (seven negative generators) from the full volume. This is essential. Their algebraic roles are different.
4. The scope of the form-uniqueness result is correctly stronger than Spin invariance. The zero form is included, and complex Hermiticity is a separate hypothesis. No positive-definite conclusion is drawn.
5. The source account is measured. It recognizes the displayed action and the older lecture's explicit freedom. It does not attribute a missing operator choice to a contradiction or imply that two distinct invariant tensors must induce different curvature operators.
6. The PBW argument for independence is valid. A later addition now proves actual generator-map independence without PBW by using the certified non-scalar full volume and the invertible first Clifford generator. This can be reported as a new formal algebraic result while leaving the full invariant-space theorem as a hand proof.

## Recommended changes before freezing

- Add a foundational formalization reference: Eric Wieser and Utensil Song, *Formalizing Geometric Algebra in Lean* (Advances in Applied Clifford Algebras 32, article 28, 2022), https://arxiv.org/abs/2110.03551. The present construction builds on an existing formal Clifford universal property and should credit that specific work, not only the general mathlib repository.
- Once VolumeTwistActual passes final replay, include its exact scope: an injective one-parameter family of actual skew generator maps. Avoid calling it a Lean proof of dim Hom_Spin >= 2.
- Keep the final number of declarations, modules, controls, and replay results in a generated artifact manifest or acceptance report. Do not guess these while the contributors are still editing.
- The phrase 'the compatible ... forms have signature (64,64)' in the baseline theorem is clearest as 'the forms represented by K and K_C have signature (64,64)'. The later classification includes the zero scalar multiple; this minor wording improvement prevents the baseline sentence from being read as including that degenerate case.

No mathematical correction was found in the invariant-space hand proof. This is not a novelty review, literature-completeness certification, or assessment of physical viability.

## Final scope pass after normalization and inner-equivalence additions

Reviewed the added normalization, rational lift, and whole-family sections against `QuadraticTwist.lean`, `GeneralBoost.lean`, `spin/RationalBoost.lean`, and `spin/LiftEquivalence.lean`.

The normalization iff, rational nontriviality, and Clifford lift have the stated scope. The rational lift theorem is equality on all Clifford elements, and its bijectivity follows from explicit inverse conjugation. The general theorem supplies an actual unit and vector identity for every point on the hyperbola, with the exceptional (-1,0) point handled explicitly. It does not assert a new general classification of representations.

The added unitarity-branch caution is mathematically necessary and correct. Negative adjoint norm cannot become positive under scalar rescaling; complex scalar rescaling multiplies that norm by an absolute-value square. The text also correctly avoids interpreting the positive rational matrix equivalence as equivalence of the full unspecified action.

The volume-square exponent is now 91. The adjoint exponent remains 105 when expanded. The revised foundational citation has the correct title, authors, venue, and DOI, checked against the arXiv primary record.

Decision: no further scope or mathematical corrections required in these sections. Final publication readiness still depends on the coordinator's integrated artifact replay and document rendering, and this review does not establish novelty or physical validity.

## Final Hermitian-family subsection

Reviewed the final H_t subsection against `spin/HermitianFamily.lean`. The formula H_t=K_C(I+t iρ_C(ω)) is Hermitian because W†K_C=K_CW. The inverse uses W²=-I and real t, so 1+t² never vanishes. Both inverse directions and invariance under actual mathlib Spin matrices are stated exactly. Nonproportionality at t=1 is over all complex scalars and is sufficient to refute the weakened uniqueness hypothesis.

The section correctly distinguishes a counterexample to Spin-only uniqueness from a counterexample to existence of the preferred form. It does not assert positive definiteness, classify all invariant forms, or quotient by coordinate changes. No further scope correction needed. Review is frozen after this pass.
