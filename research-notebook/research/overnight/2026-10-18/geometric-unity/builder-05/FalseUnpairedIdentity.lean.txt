import Client
noncomputable section
open scoped TensorProduct
open Matrix HyperbolicSpinor GUClifford GUComplex
example : ((1 + K) *ᵥ (unitCoord ∅ - K *ᵥ unitCoord ∅)) ∅ = 1 := by
  rw [unpaired_projector_kills]
  norm_num
