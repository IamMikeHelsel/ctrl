import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : (Uc.conjTranspose * Kc * Uc) {0,6} {0,6} = 2 := by
  rw [ReviewerSignature.complex_negative_value]
  norm_num
