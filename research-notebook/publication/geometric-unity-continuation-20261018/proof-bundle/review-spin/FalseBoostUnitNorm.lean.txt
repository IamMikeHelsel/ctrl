import BoostClient
open HyperbolicSpinor GUClifford BoostReview
example : star boostElement * boostElement = (1 : Cl) := by
  have h := not_unit_norm
  simp_all
