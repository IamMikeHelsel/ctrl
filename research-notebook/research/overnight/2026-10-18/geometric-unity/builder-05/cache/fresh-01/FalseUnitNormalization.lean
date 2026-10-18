import Client
noncomputable section
open scoped TensorProduct
open Matrix HyperbolicSpinor GUClifford GUComplex
example : (U.transpose * U) ∅ ∅ = 1 := by
  rw [U_orthogonal_scaled]
  norm_num
