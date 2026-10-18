import ReviewClient
noncomputable section
open HyperbolicSpinor GUClifford
example : negativeMatrix 6 * negativeMatrix 5 * negativeMatrix 4 * negativeMatrix 3 * negativeMatrix 2 * negativeMatrix 1 * negativeMatrix 0 = K := by
  rw [reversed_negative_product]
