import SkewClient
open HyperbolicSpinor GUClifford SkewReview
example : FormSkew K (splitMatrixEquiv (gamma 0) * splitMatrixEquiv (gamma 0)) := by
  have h := positive_generator_square_not_skew
  simp_all
