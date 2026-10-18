import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : K ∅ ∅ = 1 := by
  rw [K_zero_diagonal]
  norm_num
