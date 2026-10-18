import ReviewClients
open LeanControls LeanControls.QuadraticHold LeanControls.QuadraticWitness LeanControls.QuadraticIndependentReview
example : stepHold 2 1 = 0 := by
  norm_num [energy,energyRate,movingState,stepHold,DirectReference.reference_endpoint]
