import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : (U.transpose * K * U) ∅ ∅ = 1 := by
  rw [real_positive_direction]
  norm_num
