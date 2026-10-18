import BoostClient
open HyperbolicSpinor GUClifford BoostReview
example : boostElement * ((2 : ℝ) • (1 : Cl) - chirality) = (1 : Cl) := by
  have h := missing_denominator_not_inverse
  simp_all
