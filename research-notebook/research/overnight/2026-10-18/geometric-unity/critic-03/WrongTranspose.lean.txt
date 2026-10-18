import ReviewClient
noncomputable section
open HyperbolicSpinor GUClifford
example : (positiveMatrix 0).transpose = -positiveMatrix 0 := by
  rw [positive_transpose]
