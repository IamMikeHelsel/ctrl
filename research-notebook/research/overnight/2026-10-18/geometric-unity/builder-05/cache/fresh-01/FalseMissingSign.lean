import Client
noncomputable section
open scoped TensorProduct
open Matrix HyperbolicSpinor GUClifford GUComplex
example : (K *ᵥ unitCoord {0}) ({0} : Finset J)ᶜ = 1 := by
  rw [K_signed_singleton]
  simp [unitCoord]
