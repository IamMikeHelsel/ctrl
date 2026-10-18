SIGNATURE (7,7) HODGE BRIDGE

Purpose
This supplies one actual exterior/Hodge ingredient to the frozen finite-coordinate
interface. It does not implement the full Shiab or Swerve operator.

Proof sources
HodgeBridge.lean:
- V = Fin 14 -> R and its ordered coordinate basis b.
- B maps b_i to d_i times the dual basis vector. d_i is +1 for i<7 and -1 otherwise.
  metricEquiv is an explicit linear equivalence, so B is bijective.
- e k is Mathlib's exterior-power basis. vol sends the ordered top wedge to +1.
- H is exactly exteriorPower.hodgeStar B B_bijective vol.
- Bext_basis proves the induced bilinear form's diagonal action.
- H_basis proves the signed-complement formula for all complementary degrees.
- H_pairing and S_pairing use actual exterior wedge through wedgePairing.
- H_square proves H_12(H_2 x)=-x for every x in the actual degree-2 exterior space.
  H_reverse_square proves the degree-12 reverse composition.
- H_expansion extends the basis formula to arbitrary real forms.
- S is the alpha-wedge-star convention. S_basis, S_pairing, H_eq_neg_S, and
  S_square prove its formula, defining identity, relation H=-S, and square.
- subsetIndexEquiv gives a named equivalence from k-subsets to Fin (choose 14 k).
  coordinates uses the reindexed actual exterior basis. The Fin enumeration is
  chosen by Mathlib's Fintype equivalence; no lexicographic numbering is claimed.
- star2_represents and star2_signed_complement identify the actual Hodge array.

HodgeChecks.lean:
- The block-sorting permutation is related to the sorted subset lists by proofs.
- The exact subsets {0,1} and {0,7} have eps=+1.
- S_I01, H_I01, S_I07, H_I07 establish coefficients +1,-1,-1,+1 respectively.
- star2_I01 and star2_I07 establish the corresponding actual coordinate entries.
- I01_form_nonzero proves that the chosen 2-form is nonzero.
- H_square_not_positive_I01 proves that the proposed +Id square is false there.

HodgeInterface.lean:
- Imports the frozen ContractionCovariance interface.
- mathlibStar2 has exactly SwerveCoefficients.star2's type and represents H.
- conventionalStar2 has the opposite sign and represents S.
- Neither definition fills the other five fields with placeholder coefficients.

Verification
Run from any directory:
  python3 /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/weinstein/builder/verify.py

verify.py resolves Lean through the existing lean-controls Lake environment. It
copies all sources into a fresh directory under cache/, builds fresh oleans,
audits every exported target theorem, and invokes the separate leanchecker
binary. It also tries the false +Id square on the proved nonzero e_{0,1}.
verification.json and logs/ record commands, exits, versions, hashes, and axioms.
The source files and theorem proof terms are checked; no native_decide is used.
Pinned prebuilt Mathlib dependencies are reused. The Mathlib library itself is
not rebuilt from source by this verifier.

compile.py is a development helper. cache/ contains disposable development
builds. attempts/ contains exploratory API probes and their last logs. They are
not accepted proof modules. Only the three named target sources are the new proof
deliverable. The false test is kept as FalsePositiveSquare.lean.txt so it cannot be
mistaken for an accepted source module.

Limitations
This is a pointwise real exterior-algebra model. It does not define a bundle,
connection, torsion, curvature domain, spinor representation, Clifford product,
Phi tensor, or Lie algebra real form. It proves no closure, Weyl annihilation,
Bianchi identity, covariance repair, GU validity, or physical prediction.
The remaining star1/star14 and wedge arrays are not supplied. No external contact,
submission, paid service, hardware change, Git commit, push, or merge was made by
this builder. The coordinator owns notebook preservation and repository actions.
