import Client
noncomputable section
open scoped TensorProduct
open Matrix HyperbolicSpinor GUClifford GUComplex
example : (Uc.conjTranspose * Kc * Uc) {0} {0} = 2 := by
  rw [complex_negative_direction]
  norm_num
