import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : (U.transpose * U) ∅ ∅ = 1 := by
  rw [U_orthogonal_scaled]
  norm_num
