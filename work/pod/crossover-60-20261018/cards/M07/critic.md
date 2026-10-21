# M07 independent critique

The reconstructed matrix now reproduces all five nonzero determinant **magnitudes**, but only three printed signs. The sixth fixture is exactly singular with rank413. This is substantial progress on the frozen reproduction question, but it is not a six-fixture exact signed reproduction and not an ellipticity theorem.

## Source binding

The raw scan is retained at `/Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/exploration/sources/thesis-1992.pdf`; its SHA256 matches the frozen fixture JSON. I visually checked PDF73–74 and confirmed all six coefficient tuples, determinant signs and prime exponents, including3^414 in fixture(A.2) and2^526 in(A.3). All five printed nonzero determinants are negative. These scan observations are distinct from the computations below.

Section A.2 is the example driver, whereas equation(A.2) labels the second fixture. The driver's m=2*m normalization must not be applied only to fixture2 because those labels coincide. The driver also visibly assigns c2L4 while the print list/operator use c2L4p. The six printed ten-entry tuples explicitly supply the intended variable slots for these fixture experiments; a repair to the standalone example driver must remain disclosed.

Rendered PDF69–71 were checked against the new projection, injection and basis recipes. In particular, the(2,4) L4+ branch uses interior(flip(shift(flip(x⊗y)))); the(2,2) Y3 branch uses projY(flip(shift(x⊗y))); and scalar-first-factor branches retain their printed coefficients. Mathematica2's canonical signed-summand ordering remains provisional. Original sources and approved statements were preserved.

## Independent arithmetic and operator checks

`critic_symbol.py` consumes the six stored sparse448-by-448 matrices and independently uses bipartite connected components, exact rational Gauss-Jordan elimination, and row/column permutation signs. No producer determinant routine is imported. Largest components have size7. Reconstructed/source determinant ratios for the nonzero fixtures are **[1,1,−1,−1,1]**. Thus(A.1),(A.2),(A.5) match exactly; (A.3),(A.4) have opposite signs and identical magnitudes.

The singular fixture has exact rational rank413. The independent bit-mask implementation also verifies that all four projected forms vanish for the35 standard L3 blades not containingw1, while the21 containingw1 are nonzero. Those35 independent source vectors therefore span the reconstructed left kernel. This stronger source-side certificate is in critic_supplement.json.  A right-null witness is v0=−3/2,v35=3,v36=2,v37=1, all other coordinates zero. It annihilates every stored row; changing one matrix entry rejects this certificate. Because source inputs index matrix rows, this right-null vector is a target-coordinate annihilator, not yet a classified geometric source-kernel vector.

`critic_operator.py` freshly implements exterior signs and all double-form/projection operations with bit masks, then reproduces **every entry of all six matrices**. It shares only the producer's declared provisional ordered basis lists. It does not reuse the producer's exterior, symbol or determinant functions. A contraction-order sign mutation is independently distinguished. This provides a second operator evaluation with a disclosed basis-sharing boundary, not a fully independent Mathematica2 basis transcription.

A local sign discriminator was independently reproduced in critic_sign_block.json: the doubled w234-to-cleavep(w1234) entry is a(−4c1L4p+c3L4p)+3bc2L4p. For fixtures3–5 it is −5a+3b; the complementary six-dimensional minor is −768, verified by the permutation definition of determinant with freshly evaluated bit-mask entries. This supports a coefficient-dependent sign crossing rather than a blanket orientation correction.

A fixed basis permutation, orientation, or scalar normalization cannot repair just fixtures3 and4 while preserving1,2,5: it multiplies every determinant by the same factor. The mixed discrepancy therefore needs source/operator localization or a coefficient-dependent source discrepancy. Do not label it a source typo until the remaining transcription/normalization alternatives are resolved.

## Reusable normalization certificate

`critic_gram.py` independently reconstructs the support partitions and exact small Gram blocks of the scanned target basis. L4+ contributes2^-35, Y3 contributes4^70·6^28=2^168·3^28, L2 contributes1, and Y1 contributes2^31. The combined target Gram determinant is **2^164·3^28**.

For row-input coordinate matrix C and target Gram G, the source pairing matrix is C G, provided the outputs belong to the target space. Hence source pairing versus coordinate extraction changes determinant by detG; multiplying all448 matrix entries by2 adds2^448. This gives a concrete normalization discriminator instead of accepting matching ranks. It is not the determinant of the symbol itself.

Negative controls distinguish coordinate extraction from pairing using target basis diag(2,1), where the determinants differ by4; a rationally invertible diag(101,1) becomes singular modulo101; and replacing any448-by-448 matrix by its negative preserves its determinant. A transpose also preserves determinant. Consequently even six matching signed determinants would not, alone, identify every operator convention. Matrix-level witnesses and typed intermediate identities remain necessary.

Expected residues modulo101 computed from the source factorizations are[48,80,58,80,3,0]. These expected fingerprints are not reconstruction results. Bad primes2,3,5,7 collapse all reported nonzero determinants and cannot discriminate the fixtures. A nonzero valid-prime determinant establishes rational nonsingularity, whereas one zero modular determinant cannot establish rational singularity. The explicit rational null certificate above avoids that gap for the constructed sixth fixture.

## Decision

**GO** for a source-bound discrepancy-localization and certificate consumer. **HOLD** for claiming the frozen goal of all six signed determinant reproductions: two sign discrepancies remain. **NO-GO** for repairing only the two signs by an unexplained fixture-specific correction, or promoting finite covector/determinant tests directly to ellipticity or a GU physics conclusion.

The independent bit-mask reconstruction also reproduces exact determinant tests at e2,e1+e2 and−e1 for fixture1, including the predicted factor2^224 at e1+e2. These are finite metamorphic checks, not a proof of equivariance. All five critic scripts pass scoped Ruff; twenty proposed continuation mutations and positive controls are saved in critic_next_gate.json, without running that continuation block.

Next acceptance should bind the exact source-derived matrix, coefficient order, signed basis lists, pairing, scaling and determinant certificate; retain the explicit singular witness; and challenge normalization/sign mutations. Any covector covariance claim needs an actual equivariance bridge covering all nonzero covectors, not only axis/diagonal samples. Full assembly and exact arithmetic here remain Python evidence, not a kernel-checked448-dimensional reconstruction.

Quality:4/5 for independently reproduced matrix arithmetic with a sharply localized remaining discrepancy. Subjective confidence is high in the exact computations and scanned fixture transcription; the unresolved source-sign explanation and any broader geometric/physical inference remain uncertain.
