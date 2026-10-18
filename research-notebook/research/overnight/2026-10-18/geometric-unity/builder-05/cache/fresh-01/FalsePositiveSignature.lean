import Client
noncomputable section
open scoped TensorProduct
open Matrix HyperbolicSpinor GUClifford GUComplex
example : (U.transpose * K * U) {0} {0} = 2 := by
  rw [real_negative_direction]
  norm_num
