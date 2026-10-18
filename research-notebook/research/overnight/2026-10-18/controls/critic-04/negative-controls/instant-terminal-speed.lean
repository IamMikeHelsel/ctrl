import ReviewClients
open LeanControls LeanControls.QuadraticHold LeanControls.QuadraticWitness LeanControls.QuadraticIndependentReview
example : |movingState 0 1| ≤ 1/1000 := by
  norm_num [energy,energyRate,movingState,stepHold,DirectReference.reference_endpoint]
