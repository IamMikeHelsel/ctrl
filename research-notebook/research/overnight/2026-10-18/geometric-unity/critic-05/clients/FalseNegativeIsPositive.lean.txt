import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : (U.transpose * K * U) {0,6} {0,6} = 2 := by
  rw [ReviewerSignature.real_negative_value]
  norm_num
