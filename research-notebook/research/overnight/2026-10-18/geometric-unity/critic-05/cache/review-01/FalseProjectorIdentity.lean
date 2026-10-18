import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : ((1+K) *ᵥ (unitCoord ∅ - K *ᵥ unitCoord ∅)) ∅ = 1 := by
  rw [unpaired_projector_kills]
  norm_num
