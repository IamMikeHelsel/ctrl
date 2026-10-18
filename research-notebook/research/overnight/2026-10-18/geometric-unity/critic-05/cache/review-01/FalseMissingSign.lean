import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : K *ᵥ unitCoord {6} = unitCoord ({6} : Finset J)ᶜ := by
  rw [ReviewerSignature.singleton_last_sign]
  ext T
  simp [unitCoord, Pi.single_apply]
