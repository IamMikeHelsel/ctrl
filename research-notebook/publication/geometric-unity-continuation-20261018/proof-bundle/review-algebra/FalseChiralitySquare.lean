import ChiralityClient
open HyperbolicSpinor GUClifford ChiralityReview
example : (chirality * gamma 0) * (chirality * gamma 0) = (1 : Cl) := by
  have h := twisted_positive_not_positive_square
  simp_all
