import ReviewClients
open LeanControls LeanControls.QuadraticHold LeanControls.QuadraticWitness LeanControls.QuadraticIndependentReview
example : energy 16 0 0 ≤ 1 := by
  norm_num [energy,energyRate,movingState,stepHold,DirectReference.reference_endpoint]
